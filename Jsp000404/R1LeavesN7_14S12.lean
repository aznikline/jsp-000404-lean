import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10364 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 2 5 (by decide) (by decide) with h10365 | h10365
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10366 | h10366
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10367 | h10367
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10368 | h10368
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10369 | h10369
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10370 | h10370
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10371 | h10371
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10372 | h10372
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10373 | h10373
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10374 | h10374
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10375 | h10375
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10376 | h10376
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10377 | h10377
                          · linarith only [h10364, h10369, h10377, h8056, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h10364, h10368, h10369, h10377, h8056, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h10367, h10376, h8056, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h10366, h10375, h8056, hlam]
                    · linarith only [h10364, h10368, h10374, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h10364, h10367, h10368, h10369, h10373, h4610, h8056, hc01, hc12, hlam, hphi]
                · linarith only [h10364, h10366, h10369, h10372, h8056, hlam]
              · linarith only [h10369, h10371, h8056, hc02, hc25, hlam, hphi]
            · linarith only [h10364, h10368, h10369, h10370, h8056, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10387 | h10387
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10388 | h10388
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10389 | h10389
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10390 | h10390
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10391 | h10391
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10392 | h10392
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10393 | h10393
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10394 | h10394
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10395 | h10395
                            · rcases h0bigk with h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c | h10396c
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [hlam, p10396_0]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h0, hlam, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h4610, hlam, p10396_0]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h6681, hlam, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h7494, hlam, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h0, h10369, hc01, hc23, hlam, hphi, ht12, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [hlam, p10396_0]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h8056, hlam, p10396_0]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h0, h10364, h10369, h10392, h10395, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h0, h10369, h7494, hc01, hc23, hlam, hphi, ht12, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                rcases p10396_3 (m.d 0 1) (by simp) with h10407 | h10407
                                · linarith only [h10407, h4610, hlam]
                                · rcases p10396_3 (m.d 0 2) (by simp) with h10409 | h10409
                                  · linarith only [h10409, h8056, hlam]
                                  · linarith only [h0, h10409, hlam]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h10364, h10392, h10395, hc45, hlam, hphi, ht0b, ht5b, p10396_1, u0elo2]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [hlam, p10396_0]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h10364, h10392, h10395, hc45, hlam, hphi, ht0b, ht5b, p10396_1, u0elo2]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                rcases p10396_3 (m.d 0 1) (by simp) with h10415 | h10415
                                · linarith only [h10415, h4610, hlam]
                                · rcases p10396_3 (m.d 0 2) (by simp) with h10417 | h10417
                                  · linarith only [h10417, h8056, hlam]
                                  · linarith only [h10365, h10417, hlam]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h0, h10364, h10369, hc01, hc23, hlam, hphi, ht12, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h10364, hlam, p10396_0]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h10366, hlam, p10396_0]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [hlam, p10396_0]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h0, h10364, h10369, h7494, hc01, hc23, hlam, hphi, ht12, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h0, h10365, h10369, hc01, hc23, hlam, hphi, ht12, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h10365, hlam, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h10367, hlam, p10396_0]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [h10368, hlam, p10396_1]
                              · have p10396_0 := h10396c.1
                                have p10396_1 := h10396c.2.1
                                have p10396_2 := h10396c.2.2.1
                                have p10396_3 := h10396c.2.2.2
                                linarith only [hlam, p10396_0]
                            · linarith only [h0, h10364, h10369, h10394, h10395, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10431 | h10431
                            · linarith only [h10366, h10394, h10431, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c | h10433c
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [hlam, p10433_0]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h0, hlam, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h4610, hlam, p10433_0]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h6681, hlam, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h7494, hlam, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h0, h10369, hc01, hc23, hlam, hphi, ht12, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [hlam, p10433_0]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h8056, hlam, p10433_0]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h0, h10368, h10369, h10394, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h0, h10369, h7494, hc01, hc23, hlam, hphi, ht12, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                rcases p10433_3 (m.d 0 1) (by simp) with h10444 | h10444
                                · linarith only [h10444, h4610, hlam]
                                · rcases p10433_3 (m.d 0 2) (by simp) with h10446 | h10446
                                  · linarith only [h10446, h8056, hlam]
                                  · linarith only [h0, h10446, hlam]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h10364, h10392, hc34, hlam, hphi, ht0b, ht45, ht5b, p10433_1, u0elo2]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [hlam, p10433_0]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h10368, h10392, h10394, hc34, hlam, hphi, ht0b, ht45, ht5b, p10433_1, u0elo2]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h10368, h10392, h10394, hc34, hlam, hphi, ht0b, ht45, ht5b, p10433_1, u0elo2]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h0, h10364, h10369, hc01, hc23, hlam, hphi, ht12, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h10364, hlam, p10433_0]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h10366, hlam, p10433_0]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [hlam, p10433_0]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h0, h10364, h10369, h7494, hc01, hc23, hlam, hphi, ht12, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h0, h10365, h10369, hc01, hc23, hlam, hphi, ht12, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h10365, hlam, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h10367, hlam, p10433_0]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [h10368, hlam, p10433_1]
                              · have p10433_0 := h10433c.1
                                have p10433_1 := h10433c.2.1
                                have p10433_2 := h10433c.2.2.1
                                have p10433_3 := h10433c.2.2.2
                                linarith only [hlam, p10433_0]
                        · linarith only [h0, h10369, h10393, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h10369, h10392, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h10368, h10391, h6681, hlam]
                  · linarith only [h0, h10364, h10367, h10368, h10369, h10390, h4610, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10366, h10389, h4610, hlam]
              · linarith only [h0, h10365, h10388, hlam]
            · linarith only [h0, h10364, h10387, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10470 | h10470
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10471 | h10471
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10472 | h10472
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10473 | h10473
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10474 | h10474
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10475 | h10475
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10476 | h10476
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10477 | h10477
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10478 | h10478
                          · linarith only [h10364, h10368, h10470, h10478, h8056, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10480 | h10480
                            · linarith only [h10365, h10368, h10470, h10476, h10478, h10480, h6681, h8056, hc01, hc12, hlam, hphi]
                            · rcases h0bigk with h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c | h10482c
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [hlam, p10482_0]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h0, hlam, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h4610, hlam, p10482_0]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h6681, hlam, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h7494, hlam, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10470, h8056, hc01, hc12, hlam, hphi, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [hlam, p10482_0]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h8056, hlam, p10482_0]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10470, h6681, h8056, hc01, hc12, hlam, hphi, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10470, h8056, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10470, h8056, hc01, hc12, hlam, hphi, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10365, h10470, h10478, h8056, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [hlam, p10482_0]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10470, h6681, h8056, hc01, hc12, hlam, hphi, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10470, h7494, h8056, hc01, hc12, hlam, hphi, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10368, h10473, h10475, hc01, hc13, hlam, hphi, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10364, hlam, p10482_0]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10366, hlam, p10482_0]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [hlam, p10482_0]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10368, hlam, p10482_0]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10365, h10470, h8056, hc01, hc12, hlam, hphi, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10365, hlam, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10367, hlam, p10482_0]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [h10365, h10470, h8056, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10482_1]
                              · have p10482_0 := h10482c.1
                                have p10482_1 := h10482c.2.1
                                have p10482_2 := h10482c.2.2.1
                                have p10482_3 := h10482c.2.2.2
                                linarith only [hlam, p10482_0]
                        · linarith only [h10367, h10477, h8056, hlam]
                      · linarith only [h10366, h10476, h8056, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10510 | h10510
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10511 | h10511
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10512 | h10512
                          · linarith only [h10364, h10368, h10512, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10514 | h10514
                            · linarith only [h10365, h10470, h10475, h10510, h10512, h10514, h6681, h8056, hc01, hc12, hlam, hphi]
                            · rcases h0bigk with h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c | h10516c
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [hlam, p10516_0]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h0, hlam, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h4610, hlam, p10516_0]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h6681, hlam, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h7494, hlam, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10470, h8056, hc01, hc12, hlam, hphi, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [hlam, p10516_0]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h8056, hlam, p10516_0]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10470, h6681, h8056, hc01, hc12, hlam, hphi, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10470, h8056, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10470, h8056, hc01, hc12, hlam, hphi, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10365, h10470, h10512, h8056, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [hlam, p10516_0]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10470, h6681, h8056, hc01, hc12, hlam, hphi, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10470, h7494, h8056, hc01, hc12, hlam, hphi, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10475, h6681, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10364, hlam, p10516_0]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10366, hlam, p10516_0]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [hlam, p10516_0]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10368, hlam, p10516_0]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10365, h10470, h8056, hc01, hc12, hlam, hphi, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10365, hlam, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10367, hlam, p10516_0]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [h10365, h10470, h8056, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10516_1]
                              · have p10516_0 := h10516c.1
                                have p10516_1 := h10516c.2.1
                                have p10516_2 := h10516c.2.2.1
                                have p10516_3 := h10516c.2.2.2
                                linarith only [hlam, p10516_0]
                        · linarith only [h10367, h10511, h8056, hlam]
                      · linarith only [h10366, h10510, h8056, hlam]
                  · linarith only [h10365, h10367, h10474, h4610, h8056, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10364, h10366, h10470, h10473, h8056, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h10365, h10472, h8056, hc12, hc23, hlam, hphi]
            · linarith only [h10470, h10471, h8056, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10548 | h10548
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10549 | h10549
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10550 | h10550
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10551 | h10551
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10552 | h10552
                    · linarith only [h10368, h10470, h10548, h10552, h6681, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10554 | h10554
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10555 | h10555
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10556 | h10556
                          · linarith only [h10364, h10368, h10556, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10558 | h10558
                            · linarith only [h10365, h10552, h10554, h10556, h10558, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases h0bigk with h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c | h10560c
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [hlam, p10560_0]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h0, hlam, p10560_1]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h4610, hlam, p10560_0]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h6681, hlam, p10560_1]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h7494, hlam, p10560_1]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h0, h10470, hc01, hc23, hlam, hphi, ht12, p10560_1]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [hlam, p10560_0]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h8056, hlam, p10560_0]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h0, h10470, h6681, hc01, hc23, hlam, hphi, ht12, p10560_1]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h0, h10470, h7494, hc01, hc23, hlam, hphi, ht12, p10560_1]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                rcases p10560_3 (m.d 0 1) (by simp) with h10571 | h10571
                                · linarith only [h10571, h4610, hlam]
                                · rcases p10560_3 (m.d 0 2) (by simp) with h10573 | h10573
                                  · linarith only [h10573, h8056, hlam]
                                  · linarith only [h0, h10573, hlam]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h10365, h10556, hc24, hlam, hphi, ht0b, ht45, ht5b, p10560_1, u0elo2]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [hlam, p10560_0]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                rcases p10560_3 (m.d 0 1) (by simp) with h10578 | h10578
                                · linarith only [h10578, h4610, hlam]
                                · rcases p10560_3 (m.d 0 2) (by simp) with h10580 | h10580
                                  · linarith only [h10580, h8056, hlam]
                                  · linarith only [h10364, h10580, hlam]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                rcases p10560_3 (m.d 0 1) (by simp) with h10583 | h10583
                                · linarith only [h10583, h4610, hlam]
                                · rcases p10560_3 (m.d 0 2) (by simp) with h10585 | h10585
                                  · linarith only [h10585, h8056, hlam]
                                  · linarith only [h10365, h10585, hlam]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h10552, h6681, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10560_1]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h10364, hlam, p10560_0]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h10366, hlam, p10560_0]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [hlam, p10560_0]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h10368, hlam, p10560_0]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h0, h10365, h10470, hc01, hc23, hlam, hphi, ht12, p10560_1]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h10365, hlam, p10560_1]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h10367, hlam, p10560_0]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [h0, h10365, h10470, h6681, hc01, hc23, hlam, hphi, ht12, p10560_1]
                              · have p10560_0 := h10560c.1
                                have p10560_1 := h10560c.2.1
                                have p10560_2 := h10560c.2.2.1
                                have p10560_3 := h10560c.2.2.2
                                linarith only [hlam, p10560_0]
                        · linarith only [h0, h10470, h10555, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h10470, h10554, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10365, h10367, h10470, h10551, h4610, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10366, h10470, h10548, h10550, h4610, h6681, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h10365, h10549, h8056, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h0, h10364, h10548, hlam]
      · linarith only [h10365, h10367, h8056, hlam]
    · linarith only [h10364, h10366, h8056, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10606 | h10606
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10607 | h10607
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10608 | h10608
        · linarith only [h10364, h10365, h10608, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10610 | h10610
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10611 | h10611
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10612 | h10612
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10613 | h10613
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10614 | h10614
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10615 | h10615
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10616 | h10616
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10617 | h10617
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10618 | h10618
                          · linarith only [h10364, h10365, h10608, h10610, h10617, h10618, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10620 | h10620
                            · linarith only [h10364, h10365, h10616, h10618, h10620, hlam]
                            · rcases h0bigk with h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c | h10622c
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h0, hlam, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h4610, hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h6681, hlam, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h7494, hlam, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10365, h10610, h10613, h10615, h10618, hc01, hc12, hlam, hphi, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h8056, hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10365, h10610, h10613, h10615, h10618, h6681, hc01, hc12, hlam, hphi, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10365, hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10610, h8056, hc01, hc12, hlam, hphi, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10364, h10610, h8056, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10610, h6681, h8056, hc01, hc12, hlam, hphi, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10610, h7494, h8056, hc01, hc12, hlam, hphi, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10364, h10610, h8056, hc01, hc12, hlam, hphi, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10364, hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10606, hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10608, hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10365, h10610, h10613, h10615, h10618, hc01, hc12, hlam, hphi, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h0, h10365, h10610, h10613, h10615, h10618, hc01, hc12, hlam, hphi, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10607, hlam, p10622_0]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [h10365, h10610, h10613, h10615, h10618, h6681, hc01, hc12, hlam, hphi, p10622_1]
                              · have p10622_0 := h10622c.1
                                have p10622_1 := h10622c.2.1
                                have p10622_2 := h10622c.2.2.1
                                have p10622_3 := h10622c.2.2.2
                                linarith only [hlam, p10622_0]
                        · linarith only [h10607, h10617, h8056, hlam]
                      · linarith only [h10606, h10616, h8056, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10650 | h10650
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10651 | h10651
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10652 | h10652
                          · linarith only [h10364, h10615, h10652, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10654 | h10654
                            · linarith only [h10364, h10615, h10650, h10654, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases h0bigk with h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h0, hlam, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h4610, hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h6681, hlam, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h7494, hlam, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10365, h10610, h10651, hc01, hc12, hlam, hphi, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h8056, hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10365, h10610, h10651, h6681, hc01, hc12, hlam, hphi, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10365, hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10610, h8056, hc01, hc12, hlam, hphi, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10364, h10610, h8056, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10610, h6681, h8056, hc01, hc12, hlam, hphi, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10610, h7494, h8056, hc01, hc12, hlam, hphi, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10364, h10610, h8056, hc01, hc12, hlam, hphi, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10364, hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10606, hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10608, hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10365, h10610, h10651, hc01, hc12, hlam, hphi, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h0, h10365, h10610, h10651, hc01, hc12, hlam, hphi, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10607, hlam, p10656_0]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [h10365, h10610, h10651, h6681, hc01, hc12, hlam, hphi, p10656_1]
                              · have p10656_0 := h10656c.1
                                have p10656_1 := h10656c.2.1
                                have p10656_2 := h10656c.2.2.1
                                have p10656_3 := h10656c.2.2.2
                                linarith only [hlam, p10656_0]
                        · linarith only [h10607, h10651, h8056, hlam]
                      · linarith only [h10606, h10650, h8056, hlam]
                  · linarith only [h10607, h10614, h4610, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h10364, h10606, h10610, h10613, h8056, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h10364, h10610, h10612, h8056, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h10364, h10610, h10611, h8056, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10688 | h10688
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10689 | h10689
              · linarith only [h10365, h10610, h10689, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10691 | h10691
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10692 | h10692
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10693 | h10693
                    · linarith only [h10608, h10610, h10688, h10693, h6681, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10695 | h10695
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10696 | h10696
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10697 | h10697
                          · linarith only [h10364, h10693, h10697, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10699 | h10699
                            · linarith only [h0, h10689, h10697, h10699, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h0, hlam, p10701_1]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h4610, hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h6681, hlam, p10701_1]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h7494, hlam, p10701_1]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h0, h10689, hc01, hc25, hlam, hphi, ht12, p10701_1]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h8056, hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h0, h10689, h10697, hc04, hc45, hlam, hphi, p10701_1]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h10365, hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                rcases p10701_3 (m.d 0 1) (by simp) with h10712 | h10712
                                · linarith only [h10712, h4610, hlam]
                                · rcases p10701_3 (m.d 0 2) (by simp) with h10714 | h10714
                                  · linarith only [h10714, h8056, hlam]
                                  · linarith only [h0, h10714, hlam]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h10364, hc24, hlam, hphi, ht0b, ht45, ht5b, p10701_1, u0elo2]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                rcases p10701_3 (m.d 0 1) (by simp) with h10719 | h10719
                                · linarith only [h10719, h4610, hlam]
                                · rcases p10701_3 (m.d 0 2) (by simp) with h10721 | h10721
                                  · linarith only [h10721, h8056, hlam]
                                  · linarith only [h10364, h10721, hlam]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h10364, h10365, h10695, hc34, hlam, hphi, ht0b, ht45, ht5b, p10701_1, u0elo2]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h10688, h10689, h6681, hc01, hc25, hlam, hphi, ht12, p10701_1]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h10364, hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h10606, hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h10608, hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                rcases p10701_3 (m.d 0 1) (by simp) with h10730 | h10730
                                · linarith only [h10730, h7494, hlam]
                                · rcases p10701_3 (m.d 0 2) (by simp) with h10732 | h10732
                                  · linarith only [h10365, h10732, hlam]
                                  · linarith only [h0, h10732, hlam]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h10364, h10689, h10695, h10697, h7494, hc34, hc45, hlam, hphi, p10701_1]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [h10607, hlam, p10701_0]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                rcases p10701_3 (m.d 0 1) (by simp) with h10737 | h10737
                                · linarith only [h10737, h7494, hlam]
                                · rcases p10701_3 (m.d 0 2) (by simp) with h10739 | h10739
                                  · linarith only [h10365, h10739, hlam]
                                  · linarith only [h10364, h10739, hlam]
                              · have p10701_0 := h10701c.1
                                have p10701_1 := h10701c.2.1
                                have p10701_2 := h10701c.2.2.1
                                have p10701_3 := h10701c.2.2.2
                                linarith only [hlam, p10701_0]
                        · linarith only [h10607, h10610, h10696, h4610, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h10606, h10610, h10695, h4610, hlam]
                  · linarith only [h10607, h10692, h4610, hlam]
                · linarith only [h10606, h10610, h10688, h10691, h4610, h6681, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h10364, h10688, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10748 | h10748
        · linarith only [h10364, h10365, h10748, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10750 | h10750
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10751 | h10751
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10752 | h10752
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10753 | h10753
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10754 | h10754
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10755 | h10755
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10756 | h10756
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10757 | h10757
                        · linarith only [h10364, h10607, h10750, h10757, h8056, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h10364, h10750, h10754, h10756, h10757, h8056, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h10606, h10756, h8056, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10761 | h10761
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10762 | h10762
                        · linarith only [h10607, h10750, h10762, h4610, hc01, hc12, hlam, hphi]
                        · linarith only [h10364, h10750, h10754, h10761, h10762, h8056, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h10606, h10761, h8056, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10766 | h10766
                    · linarith only [h10748, h10753, h10754, h10766, h6681, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10768 | h10768
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10769 | h10769
                        · linarith only [h10750, h10754, h10769, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10771 | h10771
                          · linarith only [h10364, h10766, h10771, h7494, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10773 | h10773
                            · linarith only [h10364, h10750, h10754, h10766, h10768, h10773, h6681, h8056, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h10364, h10750, h10754, h10768, h10773, h8056, hc34, hc45, hlam, hphi]
                      · linarith only [h10364, h10606, h10768, h8056, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h10364, h10606, h10750, h10753, h8056, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h10364, h10750, h10752, h8056, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h10364, h10750, h10751, h8056, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10780 | h10780
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10781 | h10781
              · linarith only [h10364, h10365, h10750, h10781, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10783 | h10783
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10784 | h10784
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10785 | h10785
                    · linarith only [h10748, h10750, h10780, h10785, h6681, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10787 | h10787
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10788 | h10788
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10789 | h10789
                          · linarith only [h10364, h10785, h10789, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10791 | h10791
                            · linarith only [h10364, h10607, h10750, h10781, h10784, h10787, h10789, h10791, h8056, hc12, hc23, hlam, hphi]
                            · rcases h0bigk with h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c | h10793c
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [hlam, p10793_0]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h0, hlam, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h4610, hlam, p10793_0]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h6681, hlam, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h7494, hlam, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10607, h10750, h10784, h8056, hc01, hc23, hlam, hphi, ht12, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [hlam, p10793_0]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h8056, hlam, p10793_0]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10607, h10750, h10784, h6681, h8056, hc01, hc23, hlam, hphi, ht12, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10365, hlam, p10793_0]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10607, h10750, h10784, hc01, hc23, hlam, hphi, ht12, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10364, h10607, h10750, h10784, h10787, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [hlam, p10793_0]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10607, h10750, h10784, h6681, hc01, hc23, hlam, hphi, ht12, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10607, hlam, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10780, h10781, h6681, hc01, hc25, hlam, hphi, ht12, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10364, hlam, p10793_0]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10606, hlam, p10793_0]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [hlam, p10793_0]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10748, hlam, p10793_0]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10607, h10750, h10784, hc01, hc23, hlam, hphi, ht12, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10364, h10607, h10750, h10784, h10787, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10607, h10750, h10784, h4610, hc01, hc23, hlam, hphi, ht12, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [h10607, h10750, h10784, h6681, hc01, hc23, hlam, hphi, ht12, p10793_1]
                              · have p10793_0 := h10793c.1
                                have p10793_1 := h10793c.2.1
                                have p10793_2 := h10793c.2.2.1
                                have p10793_3 := h10793c.2.2.2
                                linarith only [hlam, p10793_0]
                        · linarith only [h10750, h10784, h10788, hlam]
                      · linarith only [h10606, h10750, h10787, h4610, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10821 | h10821
                    · linarith only [h10748, h10750, h10780, h10821, h6681, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10823 | h10823
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10824 | h10824
                        · linarith only [h0, h10750, h10784, h10824, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h10750, h10780, h10824, h6681, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h10606, h10750, h10780, h10823, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h10606, h10783, h4610, hlam]
            · linarith only [h0, h10364, h10780, hlam]
    · linarith only [h10364, h10606, h8056, hlam]

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h10831 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 3 4 (by decide) (by decide) with h10832 | h10832
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10833 | h10833
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10834 | h10834
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10835 | h10835
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10836 | h10836
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10837 | h10837
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10838 | h10838
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10839 | h10839
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10840 | h10840
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10841 | h10841
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10842 | h10842
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10843 | h10843
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10844 | h10844
                          · rcases h0bigk with h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c | h10845c
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [hlam, p10845_0]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h0, hlam, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h4610, hlam, p10845_0]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h6681, hlam, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h7494, hlam, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10364, h10835, h10841, hc01, hc12, hlam, hphi, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [hlam, p10845_0]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h8056, hlam, p10845_0]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10364, hlam, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10364, h10835, h10841, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10835, h8056, hc01, hc12, hlam, hphi, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10831, h10835, h8056, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [hlam, p10845_0]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10364, h10831, h10835, h10842, h8056, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10835, h7494, h8056, hc01, hc12, hlam, hphi, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10364, h10835, h10841, hc01, hc12, hlam, hphi, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10364, h10831, h10835, h10841, h10842, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10832, hlam, p10845_0]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [hlam, p10845_0]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10364, h10835, h10841, h7494, hc01, hc12, hlam, hphi, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10831, h10835, h8056, hc01, hc12, hlam, hphi, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10831, hlam, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10833, hlam, p10845_0]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [h10834, hlam, p10845_1]
                            · have p10845_0 := h10845c.1
                              have p10845_1 := h10845c.2.1
                              have p10845_2 := h10845c.2.2.1
                              have p10845_3 := h10845c.2.2.2
                              linarith only [hlam, p10845_0]
                          · linarith only [h10364, h10831, h10835, h10841, h10843, h10844, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h10364, h10834, h10843, hlam]
                      · linarith only [h10833, h10842, h8056, hlam]
                    · linarith only [h10832, h10841, h8056, hlam]
                  · linarith only [h10364, h10831, h10834, h10836, h10840, hlam]
                · linarith only [h10364, h10831, h10833, h10836, h10838, h10839, hlam]
              · linarith only [h10832, h10838, h4610, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h10831, h10835, h10837, h8056, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h10831, h10835, h10836, h8056, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10880 | h10880
          · linarith only [h10364, h10831, h10835, h10880, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10882 | h10882
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10883 | h10883
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10884 | h10884
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10885 | h10885
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10886 | h10886
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10887 | h10887
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10888 | h10888
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10889 | h10889
                          · rcases h0bigk with h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c | h10890c
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [hlam, p10890_0]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h0, hlam, p10890_1]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h4610, hlam, p10890_0]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h6681, hlam, p10890_1]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h7494, hlam, p10890_1]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h0, h10880, h10886, hc01, hc23, hlam, hphi, ht12, p10890_1]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [hlam, p10890_0]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h8056, hlam, p10890_0]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h10364, hlam, p10890_1]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h0, h10880, h10886, h7494, hc01, hc23, hlam, hphi, ht12, p10890_1]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              rcases p10890_3 (m.d 0 1) (by simp) with h10901 | h10901
                              · linarith only [h10901, h4610, hlam]
                              · rcases p10890_3 (m.d 0 2) (by simp) with h10903 | h10903
                                · linarith only [h10903, h8056, hlam]
                                · linarith only [h0, h10903, hlam]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h10831, h10887, h10889, hc45, hlam, hphi, ht0b, ht5b, p10890_1, u0elo2]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [hlam, p10890_0]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h10364, h10831, h10887, h10889, hc45, hlam, hphi, ht0b, ht5b, p10890_1, u0elo2]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              rcases p10890_3 (m.d 0 1) (by simp) with h10909 | h10909
                              · linarith only [h10909, h4610, hlam]
                              · rcases p10890_3 (m.d 0 2) (by simp) with h10911 | h10911
                                · linarith only [h10911, h8056, hlam]
                                · linarith only [h10831, h10911, hlam]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              rcases p10890_3 (m.d 0 1) (by simp) with h10914 | h10914
                              · linarith only [h10914, h6681, hlam]
                              · rcases p10890_3 (m.d 0 2) (by simp) with h10916 | h10916
                                · linarith only [h10364, h10916, hlam]
                                · linarith only [h0, h10916, hlam]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h10831, h10887, h10889, hc45, hlam, hphi, ht0b, ht5b, p10890_1, u0elo3]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h10832, hlam, p10890_0]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [hlam, p10890_0]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              rcases p10890_3 (m.d 0 1) (by simp) with h10922 | h10922
                              · linarith only [h10922, h6681, hlam]
                              · rcases p10890_3 (m.d 0 2) (by simp) with h10924 | h10924
                                · linarith only [h10364, h10924, hlam]
                                · linarith only [h10831, h10924, hlam]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h10880, h10882, h10886, h7494, hc01, hc23, hlam, hphi, ht12, p10890_1]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h10831, hlam, p10890_1]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h10833, hlam, p10890_0]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [h10834, hlam, p10890_1]
                            · have p10890_0 := h10890c.1
                              have p10890_1 := h10890c.2.1
                              have p10890_2 := h10890c.2.2.1
                              have p10890_3 := h10890c.2.2.2
                              linarith only [hlam, p10890_0]
                          · rcases h0bigk with h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c | h10932c
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [hlam, p10932_0]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h0, hlam, p10932_1]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h4610, hlam, p10932_0]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h6681, hlam, p10932_1]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h7494, hlam, p10932_1]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h0, h10880, h10886, hc01, hc23, hlam, hphi, ht12, p10932_1]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [hlam, p10932_0]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h8056, hlam, p10932_0]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10364, hlam, p10932_1]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h0, h10880, h10886, h7494, hc01, hc23, hlam, hphi, ht12, p10932_1]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              rcases p10932_3 (m.d 0 1) (by simp) with h10943 | h10943
                              · linarith only [h10943, h4610, hlam]
                              · rcases p10932_3 (m.d 0 2) (by simp) with h10945 | h10945
                                · linarith only [h10945, h8056, hlam]
                                · linarith only [h0, h10945, hlam]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10831, h10888, h10889, hc34, hlam, hphi, ht0b, ht45, ht5b, p10932_1, u0elo2]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [hlam, p10932_0]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10364, h10831, h10888, h10889, hc34, hlam, hphi, ht0b, ht45, ht5b, p10932_1, u0elo2]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10831, h10888, h10889, hc34, hlam, hphi, ht0b, ht45, ht5b, p10932_1, u0elo2]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              rcases p10932_3 (m.d 0 1) (by simp) with h10952 | h10952
                              · linarith only [h10952, h6681, hlam]
                              · rcases p10932_3 (m.d 0 2) (by simp) with h10954 | h10954
                                · linarith only [h10364, h10954, hlam]
                                · linarith only [h0, h10954, hlam]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10831, h10888, h10889, hc34, hlam, hphi, ht0b, ht45, ht5b, p10932_1, u0elo3]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10832, hlam, p10932_0]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [hlam, p10932_0]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10831, h10832, h10888, h10889, hc34, hlam, hphi, ht0b, ht45, ht5b, p10932_1, u0elo2]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10880, h10882, h10886, h7494, hc01, hc23, hlam, hphi, ht12, p10932_1]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10831, hlam, p10932_1]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10833, hlam, p10932_0]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [h10834, hlam, p10932_1]
                            · have p10932_0 := h10932c.1
                              have p10932_1 := h10932c.2.1
                              have p10932_2 := h10932c.2.2.1
                              have p10932_3 := h10932c.2.2.2
                              linarith only [hlam, p10932_0]
                        · linarith only [h0, h10880, h10888, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h10833, h10835, h10887, h4610, hlam]
                    · linarith only [h10835, h10882, h10886, h7494, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10831, h10834, h10835, h10885, h6681, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10833, h10884, h4610, hlam]
              · linarith only [h10832, h10883, h4610, hlam]
            · linarith only [h0, h10831, h10882, hlam]
      · linarith only [h10364, h10831, h10834, hlam]
    · linarith only [h10364, h10831, h10832, h10833, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10975 | h10975
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10976 | h10976
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10977 | h10977
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10978 | h10978
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10979 | h10979
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10980 | h10980
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10981 | h10981
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10982 | h10982
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10983 | h10983
                    · linarith only [h10831, h10832, h10977, h10983, h8056, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h10831, h10977, h10980, h10983, h8056, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h10976, h10982, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h10832, h10975, h10980, h10981, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10988 | h10988
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10989 | h10989
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10990 | h10990
                    · linarith only [h10977, h10980, h10990, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10992 | h10992
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10993 | h10993
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10994 | h10994
                          · rcases h0bigk with h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [hlam, p10995_0]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h0, hlam, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h4610, hlam, p10995_0]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h6681, hlam, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h7494, hlam, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10977, h10980, h8056, hc01, hc34, hlam, hphi, ht12, ht23, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [hlam, p10995_0]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h8056, hlam, p10995_0]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10364, hlam, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10977, h10980, h8056, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10977, h10980, h8056, hc01, hc34, hlam, hphi, ht12, ht23, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10977, h10980, h8056, hc02, hc34, hlam, hphi, ht23, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [hlam, p10995_0]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10832, hlam, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10977, h10980, h7494, h8056, hc01, hc34, hlam, hphi, ht12, ht23, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10364, h10978, hc01, hc12, hlam, hphi, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10831, h10992, h10994, hc45, hlam, hphi, ht0b, ht5b, p10995_1, u0elo3]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10831, h10992, h10994, h8056, hc45, hlam, hphi, ht0b, ht5b, p10995_1, u0elo3]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [hlam, p10995_0]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10364, h10978, h7494, hc01, hc12, hlam, hphi, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10831, h10977, h10980, h8056, hc01, hc34, hlam, hphi, ht12, ht23, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10831, hlam, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10975, hlam, p10995_0]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [h10976, hlam, p10995_1]
                            · have p10995_0 := h10995c.1
                              have p10995_1 := h10995c.2.1
                              have p10995_2 := h10995c.2.2.1
                              have p10995_3 := h10995c.2.2.2
                              linarith only [hlam, p10995_0]
                          · linarith only [h10831, h10977, h10980, h10992, h10994, h8056, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h10364, h10831, h10976, h10977, h10980, h10993, h6681, h8056, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h10975, h10992, h8056, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h10831, h10976, h10977, h10980, h10989, h8056, hlam]
                · linarith only [h10831, h10975, h10977, h10988, h8056, hlam]
            · linarith only [h10831, h10979, h8056, hc12, hc23, hlam, hphi]
          · linarith only [h10977, h10978, h8056, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11028 | h11028
          · linarith only [h10364, h10977, h11028, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11030 | h11030
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11031 | h11031
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11032 | h11032
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11033 | h11033
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11034 | h11034
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11035 | h11035
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11036 | h11036
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11037 | h11037
                          · rcases h0bigk with h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c | h11038c
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [hlam, p11038_0]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h0, hlam, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h4610, hlam, p11038_0]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h6681, hlam, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h7494, hlam, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h0, h11028, h11034, hc01, hc23, hlam, hphi, ht12, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [hlam, p11038_0]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h8056, hlam, p11038_0]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10364, hlam, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h0, h11028, h11034, h7494, hc01, hc23, hlam, hphi, ht12, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10832, h10977, h11031, hc01, hc23, hlam, hphi, ht12, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10831, h10832, h11035, h11037, hc45, hlam, hphi, ht0b, ht5b, p11038_1, u0elo3]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [hlam, p11038_0]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10832, hlam, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10832, h10977, h11031, h7494, hc01, hc23, hlam, hphi, ht12, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10832, h10977, h11031, hc01, hc23, hlam, hphi, ht12, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10831, h10832, h10977, h11031, h11035, h11037, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10832, h10977, h11031, h4610, hc01, hc23, hlam, hphi, ht12, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [hlam, p11038_0]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10832, h10977, h11031, h7494, hc01, hc23, hlam, hphi, ht12, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h0, h10831, h11028, h11034, hc01, hc23, hlam, hphi, ht12, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10831, hlam, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10975, hlam, p11038_0]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [h10976, hlam, p11038_1]
                            · have p11038_0 := h11038c.1
                              have p11038_1 := h11038c.2.1
                              have p11038_2 := h11038c.2.2.1
                              have p11038_3 := h11038c.2.2.2
                              linarith only [hlam, p11038_0]
                          · linarith only [h10832, h10976, h11037, hlam]
                        · linarith only [h10831, h10832, h10976, h11028, h11036, h8056, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h10832, h10977, h11031, h11035, h8056, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h10977, h11031, h11034, hlam]
                  · linarith only [h10831, h10832, h10976, h10977, h11031, h11033, h6681, h8056, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10832, h10975, h11031, h11032, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11070 | h11070
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11071 | h11071
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11072 | h11072
                    · linarith only [h10977, h11030, h11031, h11072, h7494, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h10977, h11030, h11072, h7494, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10831, h10976, h10977, h11071, h6681, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10975, h11070, h4610, hlam]
            · linarith only [h0, h10831, h11030, hlam]
      · linarith only [h10831, h10832, h10976, h8056, hlam]
    · linarith only [h10831, h10975, h8056, hlam]

end R2N4
