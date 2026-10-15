import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 0 4 5 (by decide) (by decide) with h7374 | h7374
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7375 | h7375
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7376 | h7376
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7377 | h7377
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7378 | h7378
          · linarith only [h6793, h6799, h7378, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7380 | h7380
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7381 | h7381
              · linarith only [h0, h6793, h6799, h7373, h7375, h7381, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7383 | h7383
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7384 | h7384
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7385 | h7385
                    · rcases h0bigk with h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c | h7386c
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [hlam, p7386_0]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h0, hlam, p7386_1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h0, h6793, h7375, h7383, h7385, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7386_1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h0, h6793, h6799, h7375, h7383, h7385, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7386_1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        rcases p7386_3 (m.d 0 1) (by simp) with h7391 | h7391
                        · rcases p7386_3 (m.d 0 2) (by simp) with h7392 | h7392
                          · rcases p7386_3 (m.d 0 3) (by simp) with h7393 | h7393
                            · linarith only [h6793, h7393, hlam]
                            · linarith only [h7373, h7393, hlam]
                          · linarith only [h6798, h7392, hlam]
                        · linarith only [h6795, h7391, hlam]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h6793, h7375, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7386_1, u0elo1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [hlam, p7386_0]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h6793, h7375, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7386_1, u0elo1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h6793, h6799, h7375, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7386_1, u0elo1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        rcases p7386_3 (m.d 0 1) (by simp) with h7402 | h7402
                        · linarith only [h0, h7402, hlam]
                        · linarith only [h6795, h7402, hlam]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h6793, hlam, p7386_1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h6796, hlam, p7386_1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [hlam, p7386_0]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h6799, hlam, p7386_1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        rcases p7386_3 (m.d 0 1) (by simp) with h7409 | h7409
                        · rcases p7386_3 (m.d 0 2) (by simp) with h7410 | h7410
                          · rcases p7386_3 (m.d 0 3) (by simp) with h7411 | h7411
                            · rcases p7386_3 (m.d 0 4) (by simp) with h7412 | h7412
                              · rcases p7386_3 (m.d 0 5) (by simp) with h7413 | h7413
                                · linarith only [h7373, h7413, hlam]
                                · rcases h0emin with h7415 | h7415 | h7415 | h7415 | h7415
                                  · rcases h2bigk with h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c | h7416c
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h0, hlam, p7416_1]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7416_1, u0elo1]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h7381, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7416_1, u0elo1]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      rcases p7416_3 (m.d 0 2) (by simp) with h7421 | h7421
                                      · rcases p7416_3 (m.d 1 2) (by simp) with h7422 | h7422
                                        · rcases p7416_3 (m.d 2 3) (by simp) with h7423 | h7423
                                          · linarith only [h6796, h7423, hlam]
                                          · linarith only [h7383, h7423, hlam]
                                        · linarith only [h7377, h7422, hlam]
                                      · linarith only [h7421, hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h0, h6794, h6795, h6799, h7377, h7383, h7385, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7386_1, p7416_1]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      rcases p7416_3 (m.d 0 2) (by simp) with h7430 | h7430
                                      · linarith only [h0, h7430, hlam]
                                      · linarith only [h6796, h7430, hlam]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      rcases p7416_3 (m.d 0 2) (by simp) with h7433 | h7433
                                      · linarith only [h0, h7433, hlam]
                                      · linarith only [h6797, h7433, hlam]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h0, h6794, h6795, h6799, h7377, hlam, p7386_1, p7416_2]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h6796, hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h7375, hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h7381, hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h6793, h7375, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7416_1, u0elo0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h6797, hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h7376, hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h6795, h6797, h6799, h7377, h7383, h7385, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p7386_1, p7416_1, u0elo1]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h0, h6794, h7376, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7416_1, u0elo1]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h6798, hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h7377, hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h7383, hlam, p7416_1]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [h7384, hlam, p7416_0]
                                    · have p7416_0 := h7416c.1
                                      have p7416_1 := h7416c.2.1
                                      have p7416_2 := h7416c.2.2.1
                                      have p7416_3 := h7416c.2.2.2
                                      linarith only [hlam, p7416_0]
                                  · rcases h2bigk with h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c | h7452c
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h0, hlam, p7452_1]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7452_1, u0elo1]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h7381, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7452_1, u0elo1]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      rcases p7452_3 (m.d 0 2) (by simp) with h7457 | h7457
                                      · rcases p7452_3 (m.d 1 2) (by simp) with h7458 | h7458
                                        · rcases p7452_3 (m.d 2 3) (by simp) with h7459 | h7459
                                          · linarith only [h6796, h7459, hlam]
                                          · linarith only [h7383, h7459, hlam]
                                        · linarith only [h7377, h7458, hlam]
                                      · linarith only [h7457, hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h7415, hc12, hlam, ht01, p7452_1]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      rcases p7452_3 (m.d 0 2) (by simp) with h7466 | h7466
                                      · linarith only [h0, h7466, hlam]
                                      · linarith only [h6796, h7466, hlam]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      rcases p7452_3 (m.d 0 2) (by simp) with h7469 | h7469
                                      · linarith only [h0, h7469, hlam]
                                      · linarith only [h6797, h7469, hlam]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h0, h6794, h6795, h6799, h7377, hlam, p7386_1, p7452_2]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h6796, hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h7375, hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h7381, hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h6796, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7452_1, u0elo1]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h6797, hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h7376, hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h6795, h6797, h6799, h7377, h7383, h7385, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p7386_1, p7452_1, u0elo1]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h6794, h7376, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7452_1, u0elo0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h6798, hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h7377, hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h7383, hlam, p7452_1]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [h7384, hlam, p7452_0]
                                    · have p7452_0 := h7452c.1
                                      have p7452_1 := h7452c.2.1
                                      have p7452_2 := h7452c.2.2.1
                                      have p7452_3 := h7452c.2.2.2
                                      linarith only [hlam, p7452_0]
                                  · rcases h2bigk with h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c | h7488c
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h0, hlam, p7488_1]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7488_1, u0elo1]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h7381, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7488_1, u0elo1]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      rcases p7488_3 (m.d 0 2) (by simp) with h7493 | h7493
                                      · rcases p7488_3 (m.d 1 2) (by simp) with h7494 | h7494
                                        · rcases p7488_3 (m.d 2 3) (by simp) with h7495 | h7495
                                          · linarith only [h6796, h7495, hlam]
                                          · linarith only [h7383, h7495, hlam]
                                        · linarith only [h7377, h7494, hlam]
                                      · linarith only [h7493, hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h0, h6793, h6795, h7377, h7383, h7385, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7386_1, p7488_1]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      rcases p7488_3 (m.d 0 2) (by simp) with h7502 | h7502
                                      · linarith only [h0, h7502, hlam]
                                      · linarith only [h6796, h7502, hlam]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      rcases p7488_3 (m.d 0 2) (by simp) with h7505 | h7505
                                      · linarith only [h0, h7505, hlam]
                                      · linarith only [h6797, h7505, hlam]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h0, h6794, h6795, h6799, h7377, hlam, p7386_1, p7488_2]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h6796, hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h7375, hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h7381, hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h6796, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7488_1, u0elo1]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h6797, hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h7376, hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h6795, h6797, h6799, h7377, h7383, h7385, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p7386_1, p7488_1, u0elo1]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h6794, h7376, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7488_1, u0elo0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h6798, hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h7377, hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h7383, hlam, p7488_1]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [h7384, hlam, p7488_0]
                                    · have p7488_0 := h7488c.1
                                      have p7488_1 := h7488c.2.1
                                      have p7488_2 := h7488c.2.2.1
                                      have p7488_3 := h7488c.2.2.2
                                      linarith only [hlam, p7488_0]
                                  · rcases h2bigk with h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c | h7524c
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h0, hlam, p7524_1]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7524_1, u0elo1]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h7381, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7524_1, u0elo1]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      rcases p7524_3 (m.d 0 2) (by simp) with h7529 | h7529
                                      · rcases p7524_3 (m.d 1 2) (by simp) with h7530 | h7530
                                        · rcases p7524_3 (m.d 2 3) (by simp) with h7531 | h7531
                                          · linarith only [h6796, h7531, hlam]
                                          · linarith only [h7383, h7531, hlam]
                                        · linarith only [h7377, h7530, hlam]
                                      · linarith only [h7529, hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h0, h6793, h6795, h7377, h7383, h7385, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7386_1, p7524_1]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      rcases p7524_3 (m.d 0 2) (by simp) with h7538 | h7538
                                      · linarith only [h0, h7538, hlam]
                                      · linarith only [h6796, h7538, hlam]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      rcases p7524_3 (m.d 0 2) (by simp) with h7541 | h7541
                                      · linarith only [h0, h7541, hlam]
                                      · linarith only [h6797, h7541, hlam]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h0, h6794, h6795, h6799, h7377, hlam, p7386_1, p7524_2]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h6796, hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h7375, hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h7381, hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h6796, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7524_1, u0elo1]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h6797, hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h7376, hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h6795, h6797, h6799, h7377, h7383, h7385, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p7386_1, p7524_1, u0elo1]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h6794, h7376, h7383, h7385, hc45, hlam, hphi, ht0b, ht5b, p7524_1, u0elo0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h6798, hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h7377, hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h7383, hlam, p7524_1]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [h7384, hlam, p7524_0]
                                    · have p7524_0 := h7524c.1
                                      have p7524_1 := h7524c.2.1
                                      have p7524_2 := h7524c.2.2.1
                                      have p7524_3 := h7524c.2.2.2
                                      linarith only [hlam, p7524_0]
                                  · linarith only [h6799, h7415, hc34, hlam, ht01, ht12, ht23, p7386_1]
                              · linarith only [h7374, h7412, hlam]
                            · linarith only [h7373, h7411, hlam]
                          · linarith only [h6798, h7410, hlam]
                        · linarith only [h6795, h7409, hlam]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h6794, hlam, p7386_0]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h6797, hlam, p7386_0]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h0, h6794, h6796, h7383, h7385, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7386_1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [hlam, p7386_0]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        rcases p7386_3 (m.d 0 1) (by simp) with h7569 | h7569
                        · rcases p7386_3 (m.d 0 2) (by simp) with h7570 | h7570
                          · rcases p7386_3 (m.d 0 3) (by simp) with h7571 | h7571
                            · linarith only [h6799, h7571, hlam]
                            · linarith only [h7373, h7571, hlam]
                          · linarith only [h6798, h7570, hlam]
                        · linarith only [h6795, h7569, hlam]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h6795, hlam, p7386_0]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h6798, hlam, p7386_1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h7373, hlam, p7386_0]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [h7374, hlam, p7386_1]
                      · have p7386_0 := h7386c.1
                        have p7386_1 := h7386c.2.1
                        have p7386_2 := h7386c.2.2.1
                        have p7386_3 := h7386c.2.2.2
                        linarith only [hlam, p7386_0]
                    · linarith only [h6799, h7374, h7385, hlam]
                  · linarith only [h0, h6794, h7380, h7384, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h6799, h7373, h7383, hc23, hc34, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7584 | h7584
              · linarith only [h6799, h7373, h7375, h7378, h7380, h7584, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7586 | h7586
                · linarith only [h0, h6794, h7374, h7375, h7378, h7380, h7586, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h6799, h7373, h7586, hc23, hc34, hlam, hphi]
        · linarith only [h0, h6798, h7377, hlam]
      · linarith only [h0, h6797, h7376, hlam]
    · linarith only [h0, h6796, h7375, hlam]
  · linarith only [h6799, h7373, h7374, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7594 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7595 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7596 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h7597 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h6793, h6799, h7597, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7594 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7595 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7596 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h7597 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h7599 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 2 3 4 (by decide) (by decide) with h7600 | h7600
  · linarith only [h6793, h6799, h7594, h7600, hlam]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h7602 | h7602
    · linarith only [h6793, h7373, h7594, h7602, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h7604 | h7604
      · rcases m.htr 3 4 5 (by decide) (by decide) with h7605 | h7605
        · rcases h0bigk with h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c | h7606c
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [hlam, p7606_0]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h0, hlam, p7606_1]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            rcases p7606_3 (m.d 0 1) (by simp) with h7609 | h7609
            · rcases p7606_3 (m.d 0 2) (by simp) with h7610 | h7610
              · rcases p7606_3 (m.d 0 3) (by simp) with h7611 | h7611
                · linarith only [h6793, h7611, hlam]
                · rcases p7606_3 (m.d 0 4) (by simp) with h7613 | h7613
                  · linarith only [h6794, h7613, hlam]
                  · linarith only [h6799, h7613, hlam]
              · linarith only [h6796, h7610, hlam]
            · linarith only [h6793, h7609, hlam]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h0, h7593, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7606_1]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            rcases p7606_3 (m.d 0 1) (by simp) with h7619 | h7619
            · rcases p7606_3 (m.d 0 2) (by simp) with h7620 | h7620
              · rcases p7606_3 (m.d 0 3) (by simp) with h7621 | h7621
                · linarith only [h6793, h7621, hlam]
                · rcases p7606_3 (m.d 0 4) (by simp) with h7623 | h7623
                  · linarith only [h6794, h7623, hlam]
                  · linarith only [h7593, h7623, hlam]
              · linarith only [h6798, h7620, hlam]
            · linarith only [h6795, h7619, hlam]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h6793, h7594, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7606_1, u0elo1]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [hlam, p7606_0]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            rcases p7606_3 (m.d 0 1) (by simp) with h7630 | h7630
            · linarith only [h0, h7630, hlam]
            · linarith only [h6793, h7630, hlam]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h6794, h7595, h7604, hc45, hlam, hphi, ht0b, ht5b, p7606_1, u0elo1]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            rcases p7606_3 (m.d 0 1) (by simp) with h7634 | h7634
            · linarith only [h0, h7634, hlam]
            · linarith only [h6795, h7634, hlam]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h6793, hlam, p7606_1]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h6796, hlam, p7606_1]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [hlam, p7606_0]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h6799, hlam, p7606_1]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h7373, hlam, p7606_1]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h6794, hlam, p7606_0]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h6797, hlam, p7606_0]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            rcases p7606_3 (m.d 0 1) (by simp) with h7644 | h7644
            · rcases p7606_3 (m.d 0 2) (by simp) with h7645 | h7645
              · rcases p7606_3 (m.d 0 3) (by simp) with h7646 | h7646
                · linarith only [h6799, h7646, hlam]
                · rcases p7606_3 (m.d 0 4) (by simp) with h7648 | h7648
                  · rcases p7606_3 (m.d 0 5) (by simp) with h7649 | h7649
                    · linarith only [h7593, h7649, hlam]
                    · linarith only [h7373, h7649, hlam]
                  · linarith only [h6799, h7648, hlam]
              · linarith only [h6796, h7645, hlam]
            · linarith only [h6793, h7644, hlam]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [hlam, p7606_0]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            rcases p7606_3 (m.d 0 1) (by simp) with h7656 | h7656
            · rcases p7606_3 (m.d 0 2) (by simp) with h7657 | h7657
              · rcases p7606_3 (m.d 0 3) (by simp) with h7658 | h7658
                · linarith only [h6799, h7658, hlam]
                · rcases p7606_3 (m.d 0 4) (by simp) with h7660 | h7660
                  · rcases p7606_3 (m.d 0 5) (by simp) with h7661 | h7661
                    · linarith only [h7593, h7661, hlam]
                    · rcases h0emin with h7663 | h7663 | h7663 | h7663 | h7663
                      · rcases h2bigk with h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c | h7664c
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h0, hlam, p7664_1]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          rcases p7664_3 (m.d 0 2) (by simp) with h7667 | h7667
                          · rcases p7664_3 (m.d 1 2) (by simp) with h7668 | h7668
                            · rcases p7664_3 (m.d 2 3) (by simp) with h7669 | h7669
                              · linarith only [h7669, hlam, p7664_0]
                              · rcases p7664_3 (m.d 2 4) (by simp) with h7671 | h7671
                                · linarith only [h6797, h7671, hlam]
                                · linarith only [h7600, h7671, hlam]
                            · linarith only [h7594, h7668, hlam]
                          · linarith only [h7667, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h7604, hc45, hlam, hphi, ht0b, ht5b, p7664_1, u0elo1]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          rcases p7664_3 (m.d 0 2) (by simp) with h7677 | h7677
                          · rcases p7664_3 (m.d 1 2) (by simp) with h7678 | h7678
                            · rcases p7664_3 (m.d 2 3) (by simp) with h7679 | h7679
                              · linarith only [h6796, h7679, hlam]
                              · rcases p7664_3 (m.d 2 4) (by simp) with h7681 | h7681
                                · linarith only [h6797, h7681, hlam]
                                · linarith only [h7604, h7681, hlam]
                            · linarith only [h7596, h7678, hlam]
                          · linarith only [h7677, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h0, h6793, h6794, h7373, h7594, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7606_1, p7664_1]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h0, h6793, h6794, h7373, h7594, hlam, p7606_1, p7664_2]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          rcases p7664_3 (m.d 0 2) (by simp) with h7689 | h7689
                          · linarith only [h0, h7689, hlam]
                          · linarith only [h6797, h7689, hlam]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h0, h6794, h6795, h7596, hlam, p7606_1, p7664_2]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h6796, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h7594, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h7600, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h7602, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h6797, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h7595, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h6794, h7595, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7664_1, u0elo0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h0, h6794, h7595, hc25, hlam, hphi, ht0b, ht5b, p7664_1, u0elo1]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h6798, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h7596, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7664_1, u0elo1]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [h7604, hlam, p7664_0]
                        · have p7664_0 := h7664c.1
                          have p7664_1 := h7664c.2.1
                          have p7664_2 := h7664c.2.2.1
                          have p7664_3 := h7664c.2.2.2
                          linarith only [hlam, p7664_0]
                      · rcases h2bigk with h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c | h7708c
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h0, hlam, p7708_1]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          rcases p7708_3 (m.d 0 2) (by simp) with h7711 | h7711
                          · rcases p7708_3 (m.d 1 2) (by simp) with h7712 | h7712
                            · rcases p7708_3 (m.d 2 3) (by simp) with h7713 | h7713
                              · linarith only [h7713, hlam, p7708_0]
                              · rcases p7708_3 (m.d 2 4) (by simp) with h7715 | h7715
                                · linarith only [h6797, h7715, hlam]
                                · linarith only [h7600, h7715, hlam]
                            · linarith only [h7594, h7712, hlam]
                          · linarith only [h7711, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h7604, hc45, hlam, hphi, ht0b, ht5b, p7708_1, u0elo1]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          rcases p7708_3 (m.d 0 2) (by simp) with h7721 | h7721
                          · rcases p7708_3 (m.d 1 2) (by simp) with h7722 | h7722
                            · rcases p7708_3 (m.d 2 3) (by simp) with h7723 | h7723
                              · linarith only [h6796, h7723, hlam]
                              · rcases p7708_3 (m.d 2 4) (by simp) with h7725 | h7725
                                · linarith only [h6797, h7725, hlam]
                                · linarith only [h7604, h7725, hlam]
                            · linarith only [h7596, h7722, hlam]
                          · linarith only [h7721, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h7663, hc12, hlam, ht01, p7708_1]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h0, h6793, h6794, h7373, h7594, hlam, p7606_1, p7708_2]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          rcases p7708_3 (m.d 0 2) (by simp) with h7733 | h7733
                          · linarith only [h0, h7733, hlam]
                          · linarith only [h6797, h7733, hlam]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h0, h6794, h6795, h7596, hlam, p7606_1, p7708_2]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h6796, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h7594, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h7600, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h7602, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h6797, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h7595, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h6797, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7708_1, u0elo1]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h6794, h7595, hc25, hlam, hphi, ht0b, ht5b, p7708_1, u0elo0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h6798, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h7596, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7708_1, u0elo1]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [h7604, hlam, p7708_0]
                        · have p7708_0 := h7708c.1
                          have p7708_1 := h7708c.2.1
                          have p7708_2 := h7708c.2.2.1
                          have p7708_3 := h7708c.2.2.2
                          linarith only [hlam, p7708_0]
                      · linarith only [h0, h6794, h7373, h7663, hc12, hlam, ht01, p7606_1]
                      · rcases h2bigk with h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c | h7753c
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h0, hlam, p7753_1]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          rcases p7753_3 (m.d 0 2) (by simp) with h7756 | h7756
                          · rcases p7753_3 (m.d 1 2) (by simp) with h7757 | h7757
                            · rcases p7753_3 (m.d 2 3) (by simp) with h7758 | h7758
                              · linarith only [h7758, hlam, p7753_0]
                              · rcases p7753_3 (m.d 2 4) (by simp) with h7760 | h7760
                                · linarith only [h6797, h7760, hlam]
                                · linarith only [h7600, h7760, hlam]
                            · linarith only [h7594, h7757, hlam]
                          · linarith only [h7756, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h7604, hc45, hlam, hphi, ht0b, ht5b, p7753_1, u0elo1]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          rcases p7753_3 (m.d 0 2) (by simp) with h7766 | h7766
                          · rcases p7753_3 (m.d 1 2) (by simp) with h7767 | h7767
                            · rcases p7753_3 (m.d 2 3) (by simp) with h7768 | h7768
                              · linarith only [h6796, h7768, hlam]
                              · rcases p7753_3 (m.d 2 4) (by simp) with h7770 | h7770
                                · linarith only [h6797, h7770, hlam]
                                · linarith only [h7604, h7770, hlam]
                            · linarith only [h7596, h7767, hlam]
                          · linarith only [h7766, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h0, h6794, h7373, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7606_1, p7753_1]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h0, h6794, h6796, h7373, hlam, p7606_1, p7753_2]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          rcases p7753_3 (m.d 0 2) (by simp) with h7778 | h7778
                          · linarith only [h0, h7778, hlam]
                          · linarith only [h6797, h7778, hlam]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h0, h6794, h6795, h7596, hlam, p7606_1, p7753_2]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h6796, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h7594, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h7600, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h7602, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h6797, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h7595, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h6797, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7753_1, u0elo1]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h6794, h7595, hc25, hlam, hphi, ht0b, ht5b, p7753_1, u0elo0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h6798, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h7596, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7753_1, u0elo1]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [h7604, hlam, p7753_0]
                        · have p7753_0 := h7753c.1
                          have p7753_1 := h7753c.2.1
                          have p7753_2 := h7753c.2.2.1
                          have p7753_3 := h7753c.2.2.2
                          linarith only [hlam, p7753_0]
                      · linarith only [h7663, hlam, p7606_1, u0elo3]
                  · linarith only [h7593, h7660, hlam]
              · linarith only [h6798, h7657, hlam]
            · linarith only [h6795, h7656, hlam]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h6795, hlam, p7606_0]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h6798, hlam, p7606_1]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            rcases p7606_3 (m.d 0 1) (by simp) with h7803 | h7803
            · rcases p7606_3 (m.d 0 2) (by simp) with h7804 | h7804
              · rcases p7606_3 (m.d 0 3) (by simp) with h7805 | h7805
                · linarith only [h7373, h7805, hlam]
                · rcases p7606_3 (m.d 0 4) (by simp) with h7807 | h7807
                  · rcases p7606_3 (m.d 0 5) (by simp) with h7808 | h7808
                    · rcases h0emin with h7809 | h7809 | h7809 | h7809 | h7809
                      · rcases h2bigk with h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c | h7810c
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h0, hlam, p7810_1]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          rcases p7810_3 (m.d 0 2) (by simp) with h7813 | h7813
                          · rcases p7810_3 (m.d 1 2) (by simp) with h7814 | h7814
                            · rcases p7810_3 (m.d 2 3) (by simp) with h7815 | h7815
                              · linarith only [h7815, hlam, p7810_0]
                              · rcases p7810_3 (m.d 2 4) (by simp) with h7817 | h7817
                                · linarith only [h6797, h7817, hlam]
                                · linarith only [h7600, h7817, hlam]
                            · linarith only [h7594, h7814, hlam]
                          · linarith only [h7813, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h7604, hc45, hlam, hphi, ht0b, ht5b, p7810_1, u0elo1]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          rcases p7810_3 (m.d 0 2) (by simp) with h7823 | h7823
                          · rcases p7810_3 (m.d 1 2) (by simp) with h7824 | h7824
                            · rcases p7810_3 (m.d 2 3) (by simp) with h7825 | h7825
                              · linarith only [h6796, h7825, hlam]
                              · rcases p7810_3 (m.d 2 4) (by simp) with h7827 | h7827
                                · linarith only [h6797, h7827, hlam]
                                · linarith only [h7604, h7827, hlam]
                            · linarith only [h7596, h7824, hlam]
                          · linarith only [h7823, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h0, h7809, hc12, hlam, ht01, p7810_1]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h0, h6793, h6794, h7593, h7594, hlam, p7606_1, p7810_2]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          rcases p7810_3 (m.d 0 2) (by simp) with h7835 | h7835
                          · linarith only [h0, h7835, hlam]
                          · linarith only [h6797, h7835, hlam]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          rcases p7810_3 (m.d 0 2) (by simp) with h7838 | h7838
                          · linarith only [h0, h7838, hlam]
                          · linarith only [h6798, h7838, hlam]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h6796, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h7594, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h7600, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h7602, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h6797, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h7595, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h6797, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7810_1, u0elo1]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h6794, h7595, hc25, hlam, hphi, ht0b, ht5b, p7810_1, u0elo0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h6798, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h7596, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7810_1, u0elo1]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [h7604, hlam, p7810_0]
                        · have p7810_0 := h7810c.1
                          have p7810_1 := h7810c.2.1
                          have p7810_2 := h7810c.2.2.1
                          have p7810_3 := h7810c.2.2.2
                          linarith only [hlam, p7810_0]
                      · rcases h2bigk with h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c | h7856c
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h0, hlam, p7856_1]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          rcases p7856_3 (m.d 0 2) (by simp) with h7859 | h7859
                          · rcases p7856_3 (m.d 1 2) (by simp) with h7860 | h7860
                            · rcases p7856_3 (m.d 2 3) (by simp) with h7861 | h7861
                              · linarith only [h7861, hlam, p7856_0]
                              · rcases p7856_3 (m.d 2 4) (by simp) with h7863 | h7863
                                · linarith only [h6797, h7863, hlam]
                                · linarith only [h7600, h7863, hlam]
                            · linarith only [h7594, h7860, hlam]
                          · linarith only [h7859, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h7604, hc45, hlam, hphi, ht0b, ht5b, p7856_1, u0elo1]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          rcases p7856_3 (m.d 0 2) (by simp) with h7869 | h7869
                          · rcases p7856_3 (m.d 1 2) (by simp) with h7870 | h7870
                            · rcases p7856_3 (m.d 2 3) (by simp) with h7871 | h7871
                              · linarith only [h6796, h7871, hlam]
                              · rcases p7856_3 (m.d 2 4) (by simp) with h7873 | h7873
                                · linarith only [h6797, h7873, hlam]
                                · linarith only [h7604, h7873, hlam]
                            · linarith only [h7596, h7870, hlam]
                          · linarith only [h7869, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h7809, hc12, hlam, ht01, p7856_1]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h0, h6793, h6794, h7593, h7594, hlam, p7606_1, p7856_2]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          rcases p7856_3 (m.d 0 2) (by simp) with h7881 | h7881
                          · linarith only [h0, h7881, hlam]
                          · linarith only [h6797, h7881, hlam]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          rcases p7856_3 (m.d 0 2) (by simp) with h7884 | h7884
                          · linarith only [h0, h7884, hlam]
                          · linarith only [h6798, h7884, hlam]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h6796, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h7594, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h7600, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h7602, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h6797, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h7595, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h6797, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7856_1, u0elo1]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h6794, h7595, hc25, hlam, hphi, ht0b, ht5b, p7856_1, u0elo0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h6798, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h7596, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7856_1, u0elo1]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [h7604, hlam, p7856_0]
                        · have p7856_0 := h7856c.1
                          have p7856_1 := h7856c.2.1
                          have p7856_2 := h7856c.2.2.1
                          have p7856_3 := h7856c.2.2.2
                          linarith only [hlam, p7856_0]
                      · linarith only [h7593, h7809, hlam, p7606_1, u0elo3]
                      · rcases h2bigk with h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c | h7903c
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h0, hlam, p7903_1]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          rcases p7903_3 (m.d 0 2) (by simp) with h7906 | h7906
                          · rcases p7903_3 (m.d 1 2) (by simp) with h7907 | h7907
                            · rcases p7903_3 (m.d 2 3) (by simp) with h7908 | h7908
                              · linarith only [h7908, hlam, p7903_0]
                              · rcases p7903_3 (m.d 2 4) (by simp) with h7910 | h7910
                                · linarith only [h6797, h7910, hlam]
                                · linarith only [h7600, h7910, hlam]
                            · linarith only [h7594, h7907, hlam]
                          · linarith only [h7906, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h7604, hc45, hlam, hphi, ht0b, ht5b, p7903_1, u0elo1]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          rcases p7903_3 (m.d 0 2) (by simp) with h7916 | h7916
                          · rcases p7903_3 (m.d 1 2) (by simp) with h7917 | h7917
                            · rcases p7903_3 (m.d 2 3) (by simp) with h7918 | h7918
                              · linarith only [h6796, h7918, hlam]
                              · rcases p7903_3 (m.d 2 4) (by simp) with h7920 | h7920
                                · linarith only [h6797, h7920, hlam]
                                · linarith only [h7604, h7920, hlam]
                            · linarith only [h7596, h7917, hlam]
                          · linarith only [h7916, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h0, h6794, h7593, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7606_1, p7903_1]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h0, h6793, h6794, h7593, h7594, hlam, p7606_1, p7903_2]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          rcases p7903_3 (m.d 0 2) (by simp) with h7928 | h7928
                          · linarith only [h0, h7928, hlam]
                          · linarith only [h6797, h7928, hlam]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          rcases p7903_3 (m.d 0 2) (by simp) with h7931 | h7931
                          · linarith only [h0, h7931, hlam]
                          · linarith only [h6798, h7931, hlam]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h6796, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h7594, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h7600, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h7602, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h6797, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h7595, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h6797, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7903_1, u0elo1]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h6794, h7595, hc25, hlam, hphi, ht0b, ht5b, p7903_1, u0elo0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h6798, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h7596, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7903_1, u0elo1]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [h7604, hlam, p7903_0]
                        · have p7903_0 := h7903c.1
                          have p7903_1 := h7903c.2.1
                          have p7903_2 := h7903c.2.2.1
                          have p7903_3 := h7903c.2.2.2
                          linarith only [hlam, p7903_0]
                      · rcases h2bigk with h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c | h7949c
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h0, hlam, p7949_1]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          rcases p7949_3 (m.d 0 2) (by simp) with h7952 | h7952
                          · rcases p7949_3 (m.d 1 2) (by simp) with h7953 | h7953
                            · rcases p7949_3 (m.d 2 3) (by simp) with h7954 | h7954
                              · linarith only [h7954, hlam, p7949_0]
                              · rcases p7949_3 (m.d 2 4) (by simp) with h7956 | h7956
                                · linarith only [h6797, h7956, hlam]
                                · linarith only [h7600, h7956, hlam]
                            · linarith only [h7594, h7953, hlam]
                          · linarith only [h7952, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h7604, hc45, hlam, hphi, ht0b, ht5b, p7949_1, u0elo1]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          rcases p7949_3 (m.d 0 2) (by simp) with h7962 | h7962
                          · rcases p7949_3 (m.d 1 2) (by simp) with h7963 | h7963
                            · rcases p7949_3 (m.d 2 3) (by simp) with h7964 | h7964
                              · linarith only [h6796, h7964, hlam]
                              · rcases p7949_3 (m.d 2 4) (by simp) with h7966 | h7966
                                · linarith only [h6797, h7966, hlam]
                                · linarith only [h7604, h7966, hlam]
                            · linarith only [h7596, h7963, hlam]
                          · linarith only [h7962, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h0, h6793, h6794, h7593, h7594, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7606_1, p7949_1]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h0, h6793, h6794, h7593, h7594, hlam, p7606_1, p7949_2]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          rcases p7949_3 (m.d 0 2) (by simp) with h7974 | h7974
                          · linarith only [h0, h7974, hlam]
                          · linarith only [h6797, h7974, hlam]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          rcases p7949_3 (m.d 0 2) (by simp) with h7977 | h7977
                          · linarith only [h0, h7977, hlam]
                          · linarith only [h6798, h7977, hlam]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h6796, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h7594, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h7600, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h7602, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h6797, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h7595, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h6797, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7949_1, u0elo1]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h6794, h7595, hc25, hlam, hphi, ht0b, ht5b, p7949_1, u0elo0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h6798, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h7596, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7949_1, u0elo1]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [h7604, hlam, p7949_0]
                        · have p7949_0 := h7949c.1
                          have p7949_1 := h7949c.2.1
                          have p7949_2 := h7949c.2.2.1
                          have p7949_3 := h7949c.2.2.2
                          linarith only [hlam, p7949_0]
                    · linarith only [h7373, h7808, hlam]
                  · linarith only [h6799, h7807, hlam]
              · linarith only [h6796, h7804, hlam]
            · linarith only [h6793, h7803, hlam]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [h7593, hlam, p7606_1]
          · have p7606_0 := h7606c.1
            have p7606_1 := h7606c.2.1
            have p7606_2 := h7606c.2.2.1
            have p7606_3 := h7606c.2.2.2
            linarith only [hlam, p7606_0]
        · linarith only [h6799, h7593, h7605, hlam]
      · linarith only [h0, h6794, h7599, h7604, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]

end R2N4
