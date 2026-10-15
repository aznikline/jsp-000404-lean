import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h238 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h301 | h301
  · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
    · rcases m.htr 1 2 4 (by decide) (by decide) with h303 | h303
      · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
        · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
          · linarith only [h1, h305, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
            · linarith only [h1, h238, h307, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
              · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                · linarith only [h0, h310, h4, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                  · linarith only [h1, h238, h302, h312, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h314 | h314
                    · linarith only [h0, h303, h314, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h2, h309, h314, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
                · linarith only [h301, h302, h305, h309, h317, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h319 | h319
                  · linarith only [h238, h301, h302, h305, h309, h319, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h321 | h321
                    · linarith only [h0, h302, h305, h309, h321, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h323 | h323
                      · rcases h0bigk with h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c | h324c
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          rcases p324_3 (m.d 0 1) (by simp) with h327 | h327
                          · rcases p324_3 (m.d 0 2) (by simp) with h328 | h328
                            · linarith only [h0, h328, hlam]
                            · linarith only [h328, h4, hlam]
                          · linarith only [h1, h327, hlam]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h301, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h301, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h0, hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          rcases p324_3 (m.d 0 1) (by simp) with h336 | h336
                          · rcases p324_3 (m.d 0 2) (by simp) with h337 | h337
                            · rcases p324_3 (m.d 0 3) (by simp) with h338 | h338
                              · linarith only [h338, h4, hlam]
                              · rcases p324_3 (m.d 0 4) (by simp) with h340 | h340
                                · linarith only [h340, h5, hlam]
                                · linarith only [h340, h7, hlam]
                            · linarith only [h337, h4, hlam]
                          · linarith only [h1, h336, hlam]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h301, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h0, h301, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h1, hlam, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h4, hlam, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h7, hlam, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h238, hlam, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h2, hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h5, hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          rcases p324_3 (m.d 0 1) (by simp) with h354 | h354
                          · rcases p324_3 (m.d 0 2) (by simp) with h355 | h355
                            · rcases p324_3 (m.d 0 3) (by simp) with h356 | h356
                              · linarith only [h356, h7, hlam]
                              · rcases p324_3 (m.d 0 4) (by simp) with h358 | h358
                                · rcases p324_3 (m.d 0 5) (by simp) with h359 | h359
                                  · linarith only [h301, h359, hlam]
                                  · linarith only [h238, h359, hlam]
                                · linarith only [h358, h7, hlam]
                            · linarith only [h355, h4, hlam]
                          · linarith only [h1, h354, hlam]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h301, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p324_1, u0elo3]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h3, hlam, p324_0]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h6, hlam, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          rcases p324_3 (m.d 0 1) (by simp) with h369 | h369
                          · rcases p324_3 (m.d 0 2) (by simp) with h370 | h370
                            · rcases p324_3 (m.d 0 3) (by simp) with h371 | h371
                              · linarith only [h238, h371, hlam]
                              · rcases p324_3 (m.d 0 4) (by simp) with h373 | h373
                                · rcases p324_3 (m.d 0 5) (by simp) with h374 | h374
                                  · rcases h0emin with h375 | h375 | h375 | h375 | h375
                                    · rcases h1bigk with h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p376_1, u0elo0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        rcases p376_3 (m.d 0 1) (by simp) with h379 | h379
                                        · rcases p376_3 (m.d 1 2) (by simp) with h380 | h380
                                          · linarith only [h0, h380, hlam]
                                          · linarith only [h302, h380, hlam]
                                        · linarith only [h379, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        rcases p376_3 (m.d 0 1) (by simp) with h384 | h384
                                        · rcases p376_3 (m.d 1 2) (by simp) with h385 | h385
                                          · linarith only [h0, h385, hlam]
                                          · linarith only [h303, h385, hlam]
                                        · linarith only [h384, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        rcases p376_3 (m.d 0 1) (by simp) with h389 | h389
                                        · rcases p376_3 (m.d 1 2) (by simp) with h390 | h390
                                          · linarith only [h0, h390, hlam]
                                          · linarith only [h304, h390, hlam]
                                        · linarith only [h389, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h0, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h0, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p376_1, u0elo0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h0, h302, h305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p376_1, u0elo0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h0, h302, h305, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p376_1, u0elo0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h302, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h305, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h307, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h2, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h303, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h302, h309, hc23, hc45, hlam, hphi, ht34, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h309, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h3, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h304, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h0, h302, h304, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p376_1, u0elo0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h0, h304, hc14, hlam, hphi, ht0b, ht45, ht5b, p376_1, u0elo0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                    · rcases h1bigk with h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h304, hc25, hlam, hphi, ht0b, ht5b, p414_1, u0elo0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        rcases p414_3 (m.d 0 1) (by simp) with h417 | h417
                                        · rcases p414_3 (m.d 1 2) (by simp) with h418 | h418
                                          · linarith only [h0, h418, hlam]
                                          · linarith only [h302, h418, hlam]
                                        · linarith only [h417, hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        rcases p414_3 (m.d 0 1) (by simp) with h422 | h422
                                        · rcases p414_3 (m.d 1 2) (by simp) with h423 | h423
                                          · linarith only [h0, h423, hlam]
                                          · linarith only [h303, h423, hlam]
                                        · linarith only [h422, hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        rcases p414_3 (m.d 0 1) (by simp) with h427 | h427
                                        · rcases p414_3 (m.d 1 2) (by simp) with h428 | h428
                                          · linarith only [h0, h428, hlam]
                                          · linarith only [h304, h428, hlam]
                                        · linarith only [h427, hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h0, hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h0, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p414_1, u0elo0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h0, h302, h305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p414_1, u0elo0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h0, hc15, hlam, hphi, ht0b, ht5b, p414_1, u0elo0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h1, hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h302, hlam, p414_1]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h305, hlam, p414_1]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h307, hlam, p414_1]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h2, hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h303, hlam, p414_1]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h2, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p414_1, u0elo0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h309, hlam, p414_1]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h3, hlam, p414_0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h304, hlam, p414_1]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h3, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p414_1, u0elo0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [h0, h301, h309, h5, hc14, hlam, hphi, ht0b, ht45, ht5b, p414_1, u0elo0]
                                      · have p414_0 := h414c.1
                                        have p414_1 := h414c.2.1
                                        have p414_2 := h414c.2.2.1
                                        have p414_3 := h414c.2.2.2
                                        linarith only [hlam, p414_0]
                                    · linarith only [h375, hlam, p324_1, u0elo4]
                                    · rcases h1bigk with h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p453_1, u0elo0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        rcases p453_3 (m.d 0 1) (by simp) with h456 | h456
                                        · rcases p453_3 (m.d 1 2) (by simp) with h457 | h457
                                          · linarith only [h0, h457, hlam]
                                          · linarith only [h302, h457, hlam]
                                        · linarith only [h456, hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        rcases p453_3 (m.d 0 1) (by simp) with h461 | h461
                                        · rcases p453_3 (m.d 1 2) (by simp) with h462 | h462
                                          · linarith only [h0, h462, hlam]
                                          · linarith only [h303, h462, hlam]
                                        · linarith only [h461, hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        rcases p453_3 (m.d 0 1) (by simp) with h466 | h466
                                        · rcases p453_3 (m.d 1 2) (by simp) with h467 | h467
                                          · linarith only [h0, h467, hlam]
                                          · linarith only [h304, h467, hlam]
                                        · linarith only [h466, hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h0, hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h0, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p453_1, u0elo0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h0, h303, h317, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p453_1, u0elo0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h0, hc15, hlam, hphi, ht0b, ht5b, p453_1, u0elo0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h1, hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h302, hlam, p453_1]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h305, hlam, p453_1]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h307, hlam, p453_1]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h2, hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h303, hlam, p453_1]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h2, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p453_1, u0elo0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h309, hlam, p453_1]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h3, hlam, p453_0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h304, hlam, p453_1]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h3, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p453_1, u0elo0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [h0, h301, h309, h5, hc14, hlam, hphi, ht0b, ht45, ht5b, p453_1, u0elo0]
                                      · have p453_0 := h453c.1
                                        have p453_1 := h453c.2.1
                                        have p453_2 := h453c.2.2.1
                                        have p453_3 := h453c.2.2.2
                                        linarith only [hlam, p453_0]
                                    · rcases h1bigk with h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p491_1, u0elo0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        rcases p491_3 (m.d 0 1) (by simp) with h494 | h494
                                        · rcases p491_3 (m.d 1 2) (by simp) with h495 | h495
                                          · linarith only [h0, h495, hlam]
                                          · linarith only [h302, h495, hlam]
                                        · linarith only [h494, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        rcases p491_3 (m.d 0 1) (by simp) with h499 | h499
                                        · rcases p491_3 (m.d 1 2) (by simp) with h500 | h500
                                          · linarith only [h0, h500, hlam]
                                          · linarith only [h303, h500, hlam]
                                        · linarith only [h499, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        rcases p491_3 (m.d 0 1) (by simp) with h504 | h504
                                        · rcases p491_3 (m.d 1 2) (by simp) with h505 | h505
                                          · linarith only [h0, h505, hlam]
                                          · linarith only [h304, h505, hlam]
                                        · linarith only [h504, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h0, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h0, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p491_1, u0elo0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h0, h303, h317, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p491_1, u0elo0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h0, hc15, hlam, hphi, ht0b, ht5b, p491_1, u0elo0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h1, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h302, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h305, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h307, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h2, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h303, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h2, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p491_1, u0elo0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h309, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h3, hlam, p491_0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h304, hlam, p491_1]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h3, h302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p491_1, u0elo0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [h0, h301, h309, h5, hc14, hlam, hphi, ht0b, ht45, ht5b, p491_1, u0elo0]
                                      · have p491_0 := h491c.1
                                        have p491_1 := h491c.2.1
                                        have p491_2 := h491c.2.2.1
                                        have p491_3 := h491c.2.2.2
                                        linarith only [hlam, p491_0]
                                  · linarith only [h238, h374, hlam]
                                · linarith only [h373, h7, hlam]
                            · linarith only [h370, h4, hlam]
                          · linarith only [h1, h369, hlam]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [h301, hlam, p324_1]
                        · have p324_0 := h324c.1
                          have p324_1 := h324c.2.1
                          have p324_2 := h324c.2.2.1
                          have p324_3 := h324c.2.2.2
                          linarith only [hlam, p324_0]
                      · linarith only [h301, h323, h7, hlam]
        · linarith only [h0, h302, h304, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · linarith only [h0, h302, h303, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h538 | h538
      · linarith only [h0, h302, h4, h538, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h540 | h540
        · linarith only [h0, h302, h4, h540, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h542 | h542
          · linarith only [h1, h542, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h544 | h544
            · linarith only [h1, h238, h302, h4, h544, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h546 | h546
              · rcases m.htr 2 3 4 (by decide) (by decide) with h547 | h547
                · linarith only [h4, h547, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h549 | h549
                  · linarith only [h238, h4, h549, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h551 | h551
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h552 | h552
                      · rcases h0bigk with h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c | h553c
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [hlam, p553_0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h302, h5, h549, h551, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p553_1, u0elo0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h302, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p553_1, u0elo0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h2, h546, hc45, hlam, hphi, ht0b, ht5b, p553_1, u0elo0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h302, h549, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p553_1, u0elo0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h0, hlam, p553_0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [hlam, p553_0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h302, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p553_1, u0elo1]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h0, h302, h5, h549, h551, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p553_1, u0elo0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h0, h302, h549, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p553_1, u0elo0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h1, hlam, p553_1]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h4, hlam, p553_1]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [hlam, p553_0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h7, hlam, p553_1]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h238, hlam, p553_1]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h2, hlam, p553_0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h5, hlam, p553_0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h302, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p553_1, u0elo3]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [hlam, p553_0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h0, h302, h5, h549, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p553_1, u0elo0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h3, hlam, p553_0]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h6, hlam, p553_1]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h302, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p553_1, u0elo4]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [h301, hlam, p553_1]
                        · have p553_0 := h553c.1
                          have p553_1 := h553c.2.1
                          have p553_2 := h553c.2.2.1
                          have p553_3 := h553c.2.2.2
                          linarith only [hlam, p553_0]
                      · linarith only [h302, h4, h552, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h2, h546, h551, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h581 | h581
                · linarith only [h301, h302, h4, h542, h546, h581, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h583 | h583
                  · linarith only [h0, h238, h5, h581, h583, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h585 | h585
                    · linarith only [h0, h302, h5, h542, h546, h585, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h301, h538, h585, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
    · rcases m.htr 1 2 4 (by decide) (by decide) with h589 | h589
      · rcases m.htr 1 2 5 (by decide) (by decide) with h590 | h590
        · rcases m.htr 1 3 4 (by decide) (by decide) with h591 | h591
          · linarith only [h1, h591, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h593 | h593
            · linarith only [h1, h238, h593, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h595 | h595
              · linarith only [h2, h301, h595, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h597 | h597
                · linarith only [h1, h588, h597, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h599 | h599
                  · linarith only [h1, h238, h588, h599, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h601 | h601
                    · linarith only [h0, h1, h301, h5, h588, h601, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h603 | h603
                      · rcases h0bigk with h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [hlam, p604_0]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p604_1, u0elo0]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          rcases p604_3 (m.d 0 1) (by simp) with h607 | h607
                          · rcases p604_3 (m.d 0 2) (by simp) with h608 | h608
                            · linarith only [h0, h608, hlam]
                            · linarith only [h4, h608, hlam]
                          · linarith only [h1, h607, hlam]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          rcases p604_3 (m.d 0 1) (by simp) with h612 | h612
                          · rcases p604_3 (m.d 0 2) (by simp) with h613 | h613
                            · linarith only [h0, h613, hlam]
                            · linarith only [h5, h613, hlam]
                          · linarith only [h2, h612, hlam]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          rcases p604_3 (m.d 0 1) (by simp) with h617 | h617
                          · rcases p604_3 (m.d 0 2) (by simp) with h618 | h618
                            · linarith only [h0, h618, hlam]
                            · linarith only [h6, h618, hlam]
                          · linarith only [h3, h617, hlam]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h0, hlam, p604_0]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [hlam, p604_0]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          rcases p604_3 (m.d 0 1) (by simp) with h624 | h624
                          · rcases p604_3 (m.d 0 2) (by simp) with h625 | h625
                            · rcases p604_3 (m.d 0 3) (by simp) with h626 | h626
                              · linarith only [h4, h626, hlam]
                              · rcases p604_3 (m.d 0 4) (by simp) with h628 | h628
                                · linarith only [h5, h628, hlam]
                                · linarith only [h628, h7, hlam]
                            · linarith only [h4, h625, hlam]
                          · linarith only [h1, h624, hlam]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          rcases p604_3 (m.d 0 1) (by simp) with h633 | h633
                          · rcases p604_3 (m.d 0 2) (by simp) with h634 | h634
                            · rcases p604_3 (m.d 0 3) (by simp) with h635 | h635
                              · linarith only [h4, h635, hlam]
                              · rcases p604_3 (m.d 0 4) (by simp) with h637 | h637
                                · linarith only [h5, h637, hlam]
                                · rcases p604_3 (m.d 0 5) (by simp) with h639 | h639
                                  · linarith only [h6, h639, hlam]
                                  · linarith only [h301, h639, hlam]
                            · linarith only [h5, h634, hlam]
                          · linarith only [h2, h633, hlam]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          rcases p604_3 (m.d 0 1) (by simp) with h644 | h644
                          · rcases p604_3 (m.d 0 2) (by simp) with h645 | h645
                            · rcases p604_3 (m.d 0 3) (by simp) with h646 | h646
                              · linarith only [h4, h646, hlam]
                              · rcases p604_3 (m.d 0 4) (by simp) with h648 | h648
                                · linarith only [h5, h648, hlam]
                                · rcases p604_3 (m.d 0 5) (by simp) with h650 | h650
                                  · linarith only [h6, h650, hlam]
                                  · rcases h0emin with h652 | h652 | h652 | h652 | h652
                                    · rcases h1bigk with h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h590, h597, h601, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p653_1, u0elo0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        rcases p653_3 (m.d 0 1) (by simp) with h656 | h656
                                        · rcases p653_3 (m.d 1 2) (by simp) with h657 | h657
                                          · linarith only [h0, h657, hlam]
                                          · linarith only [h588, h657, hlam]
                                        · linarith only [h656, hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        rcases p653_3 (m.d 0 1) (by simp) with h661 | h661
                                        · rcases p653_3 (m.d 1 2) (by simp) with h662 | h662
                                          · linarith only [h0, h662, hlam]
                                          · linarith only [h589, h662, hlam]
                                        · linarith only [h661, hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        rcases p653_3 (m.d 0 1) (by simp) with h666 | h666
                                        · rcases p653_3 (m.d 1 2) (by simp) with h667 | h667
                                          · linarith only [h0, h667, hlam]
                                          · linarith only [h590, h667, hlam]
                                        · linarith only [h666, hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h0, hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h0, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p653_1, u0elo0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h0, h588, h591, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p653_1, u0elo0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h0, h588, h591, h595, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p653_1, u0elo0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h1, hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h588, hlam, p653_1]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h591, hlam, p653_1]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h593, hlam, p653_1]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h2, hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h589, hlam, p653_1]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h2, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p653_1, u0elo0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h595, hlam, p653_1]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h3, hlam, p653_0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h590, hlam, p653_1]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h3, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p653_1, u0elo0]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p604_1, p653_1, u0elo1]
                                      · have p653_0 := h653c.1
                                        have p653_1 := h653c.2.1
                                        have p653_2 := h653c.2.2.1
                                        have p653_3 := h653c.2.2.2
                                        linarith only [hlam, p653_0]
                                    · rcases h1bigk with h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p691_1, u0elo0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        rcases p691_3 (m.d 0 1) (by simp) with h694 | h694
                                        · rcases p691_3 (m.d 1 2) (by simp) with h695 | h695
                                          · linarith only [h0, h695, hlam]
                                          · linarith only [h588, h695, hlam]
                                        · linarith only [h694, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        rcases p691_3 (m.d 0 1) (by simp) with h699 | h699
                                        · rcases p691_3 (m.d 1 2) (by simp) with h700 | h700
                                          · linarith only [h0, h700, hlam]
                                          · linarith only [h589, h700, hlam]
                                        · linarith only [h699, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        rcases p691_3 (m.d 0 1) (by simp) with h704 | h704
                                        · rcases p691_3 (m.d 1 2) (by simp) with h705 | h705
                                          · linarith only [h0, h705, hlam]
                                          · linarith only [h590, h705, hlam]
                                        · linarith only [h704, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h0, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h0, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p691_1, u0elo0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h0, h589, h597, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p691_1, u0elo0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h0, hc15, hlam, hphi, ht0b, ht5b, p691_1, u0elo0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h1, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h588, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h591, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h593, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h2, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h589, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h2, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p691_1, u0elo0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h595, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h3, hlam, p691_0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h590, hlam, p691_1]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h3, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p691_1, u0elo0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [h0, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p604_1, p691_1, u0elo0]
                                      · have p691_0 := h691c.1
                                        have p691_1 := h691c.2.1
                                        have p691_2 := h691c.2.2.1
                                        have p691_3 := h691c.2.2.2
                                        linarith only [hlam, p691_0]
                                    · linarith only [h0, h301, h652, h7, hlam, p604_1, u0elo0]
                                    · linarith only [h0, h301, h652, hlam, p604_1, u0elo0]
                                    · linarith only [h0, h652, hlam, p604_1, u0elo0]
                            · linarith only [h6, h645, hlam]
                          · linarith only [h3, h644, hlam]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h1, hlam, p604_1]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h4, hlam, p604_1]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [hlam, p604_0]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h7, hlam, p604_1]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h238, hlam, p604_1]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h2, hlam, p604_0]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h5, hlam, p604_0]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h301, h603, hc03, hc34, hlam, hphi, p604_1]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [hlam, p604_0]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h301, hlam, p604_0]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h3, hlam, p604_0]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h6, hlam, p604_1]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h1, h301, h588, h603, hc23, hc34, hlam, hphi, p604_1]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [h301, h5, h597, h603, hc23, hc34, hlam, hphi, p604_1]
                        · have p604_0 := h604c.1
                          have p604_1 := h604c.2.1
                          have p604_2 := h604c.2.2.1
                          have p604_3 := h604c.2.2.2
                          linarith only [hlam, p604_0]
                      · rcases h0bigk with h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p749_1, u0elo0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 1) (by simp) with h752 | h752
                          · rcases p749_3 (m.d 0 2) (by simp) with h753 | h753
                            · linarith only [h0, h753, hlam]
                            · linarith only [h4, h753, hlam]
                          · linarith only [h1, h752, hlam]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 1) (by simp) with h757 | h757
                          · rcases p749_3 (m.d 0 2) (by simp) with h758 | h758
                            · linarith only [h0, h758, hlam]
                            · linarith only [h5, h758, hlam]
                          · linarith only [h2, h757, hlam]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 1) (by simp) with h762 | h762
                          · rcases p749_3 (m.d 0 2) (by simp) with h763 | h763
                            · linarith only [h0, h763, hlam]
                            · linarith only [h6, h763, hlam]
                          · linarith only [h3, h762, hlam]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h0, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 1) (by simp) with h769 | h769
                          · rcases p749_3 (m.d 0 2) (by simp) with h770 | h770
                            · rcases p749_3 (m.d 0 3) (by simp) with h771 | h771
                              · linarith only [h4, h771, hlam]
                              · rcases p749_3 (m.d 0 4) (by simp) with h773 | h773
                                · linarith only [h5, h773, hlam]
                                · linarith only [h7, h773, hlam]
                            · linarith only [h4, h770, hlam]
                          · linarith only [h1, h769, hlam]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 1) (by simp) with h778 | h778
                          · rcases p749_3 (m.d 0 2) (by simp) with h779 | h779
                            · rcases p749_3 (m.d 0 3) (by simp) with h780 | h780
                              · linarith only [h4, h780, hlam]
                              · rcases p749_3 (m.d 0 4) (by simp) with h782 | h782
                                · linarith only [h5, h782, hlam]
                                · rcases p749_3 (m.d 0 5) (by simp) with h784 | h784
                                  · linarith only [h6, h784, hlam]
                                  · linarith only [h301, h784, hlam]
                            · linarith only [h5, h779, hlam]
                          · linarith only [h2, h778, hlam]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 1) (by simp) with h789 | h789
                          · rcases p749_3 (m.d 0 2) (by simp) with h790 | h790
                            · rcases p749_3 (m.d 0 3) (by simp) with h791 | h791
                              · linarith only [h4, h791, hlam]
                              · rcases p749_3 (m.d 0 4) (by simp) with h793 | h793
                                · linarith only [h5, h793, hlam]
                                · rcases p749_3 (m.d 0 5) (by simp) with h795 | h795
                                  · linarith only [h6, h795, hlam]
                                  · rcases h0emin with h797 | h797 | h797 | h797 | h797
                                    · rcases h1bigk with h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h590, h601, hc24, hlam, hphi, ht0b, ht45, ht5b, p798_1, u0elo0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        rcases p798_3 (m.d 0 1) (by simp) with h801 | h801
                                        · rcases p798_3 (m.d 1 2) (by simp) with h802 | h802
                                          · linarith only [h0, h802, hlam]
                                          · linarith only [h588, h802, hlam]
                                        · linarith only [h801, hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        rcases p798_3 (m.d 0 1) (by simp) with h806 | h806
                                        · rcases p798_3 (m.d 1 2) (by simp) with h807 | h807
                                          · linarith only [h0, h807, hlam]
                                          · linarith only [h589, h807, hlam]
                                        · linarith only [h806, hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        rcases p798_3 (m.d 0 1) (by simp) with h811 | h811
                                        · rcases p798_3 (m.d 1 2) (by simp) with h812 | h812
                                          · linarith only [h0, h812, hlam]
                                          · linarith only [h590, h812, hlam]
                                        · linarith only [h811, hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h0, hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h0, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p798_1, u0elo0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h0, h588, h591, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p798_1, u0elo0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h0, hc15, hlam, hphi, ht0b, ht5b, p798_1, u0elo0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h1, hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h588, hlam, p798_1]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h591, hlam, p798_1]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h593, hlam, p798_1]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h2, hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h589, hlam, p798_1]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h2, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p798_1, u0elo0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h595, hlam, p798_1]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h3, hlam, p798_0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h590, hlam, p798_1]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h3, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p798_1, u0elo0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [h0, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p749_1, p798_1, u0elo0]
                                      · have p798_0 := h798c.1
                                        have p798_1 := h798c.2.1
                                        have p798_2 := h798c.2.2.1
                                        have p798_3 := h798c.2.2.2
                                        linarith only [hlam, p798_0]
                                    · rcases h1bigk with h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p836_1, u0elo0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        rcases p836_3 (m.d 0 1) (by simp) with h839 | h839
                                        · rcases p836_3 (m.d 1 2) (by simp) with h840 | h840
                                          · linarith only [h0, h840, hlam]
                                          · linarith only [h588, h840, hlam]
                                        · linarith only [h839, hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        rcases p836_3 (m.d 0 1) (by simp) with h844 | h844
                                        · rcases p836_3 (m.d 1 2) (by simp) with h845 | h845
                                          · linarith only [h0, h845, hlam]
                                          · linarith only [h589, h845, hlam]
                                        · linarith only [h844, hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        rcases p836_3 (m.d 0 1) (by simp) with h849 | h849
                                        · rcases p836_3 (m.d 1 2) (by simp) with h850 | h850
                                          · linarith only [h0, h850, hlam]
                                          · linarith only [h590, h850, hlam]
                                        · linarith only [h849, hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h0, hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h0, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p836_1, u0elo0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h0, h589, h597, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p836_1, u0elo0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h0, hc15, hlam, hphi, ht0b, ht5b, p836_1, u0elo0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h1, hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h588, hlam, p836_1]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h591, hlam, p836_1]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h593, hlam, p836_1]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h2, hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h589, hlam, p836_1]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h2, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p836_1, u0elo0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h595, hlam, p836_1]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h3, hlam, p836_0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h590, hlam, p836_1]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h3, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p836_1, u0elo0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [h0, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p749_1, p836_1, u0elo0]
                                      · have p836_0 := h836c.1
                                        have p836_1 := h836c.2.1
                                        have p836_2 := h836c.2.2.1
                                        have p836_3 := h836c.2.2.2
                                        linarith only [hlam, p836_0]
                                    · linarith only [h0, h301, h7, h797, hlam, p749_1, u0elo0]
                                    · linarith only [h0, h301, h797, hlam, p749_1, u0elo0]
                                    · linarith only [h0, h797, hlam, p749_1, u0elo0]
                            · linarith only [h6, h790, hlam]
                          · linarith only [h3, h789, hlam]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h1, hlam, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h4, hlam, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h7, hlam, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h238, hlam, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h2, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h5, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h1, h301, h588, hc23, hc45, hlam, hphi, ht34, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h301, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h3, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h6, hlam, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 1) (by simp) with h891 | h891
                          · rcases p749_3 (m.d 0 2) (by simp) with h892 | h892
                            · rcases p749_3 (m.d 0 3) (by simp) with h893 | h893
                              · linarith only [h238, h893, hlam]
                              · rcases p749_3 (m.d 0 4) (by simp) with h895 | h895
                                · linarith only [h301, h895, hlam]
                                · linarith only [h7, h895, hlam]
                            · linarith only [h4, h892, hlam]
                          · linarith only [h1, h891, hlam]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 1) (by simp) with h900 | h900
                          · rcases p749_3 (m.d 0 2) (by simp) with h901 | h901
                            · rcases p749_3 (m.d 0 3) (by simp) with h902 | h902
                              · linarith only [h238, h902, hlam]
                              · rcases p749_3 (m.d 0 4) (by simp) with h904 | h904
                                · linarith only [h301, h904, hlam]
                                · rcases p749_3 (m.d 0 5) (by simp) with h906 | h906
                                  · rcases h0emin with h907 | h907 | h907 | h907 | h907
                                    · rcases h1bigk with h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        rcases p908_3 (m.d 0 1) (by simp) with h911 | h911
                                        · rcases p908_3 (m.d 1 2) (by simp) with h912 | h912
                                          · linarith only [h0, h912, hlam]
                                          · linarith only [h588, h912, hlam]
                                        · linarith only [h911, hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        rcases p908_3 (m.d 0 1) (by simp) with h916 | h916
                                        · rcases p908_3 (m.d 1 2) (by simp) with h917 | h917
                                          · linarith only [h0, h917, hlam]
                                          · linarith only [h589, h917, hlam]
                                        · linarith only [h916, hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        rcases p908_3 (m.d 0 1) (by simp) with h921 | h921
                                        · rcases p908_3 (m.d 1 2) (by simp) with h922 | h922
                                          · linarith only [h0, h922, hlam]
                                          · linarith only [h590, h922, hlam]
                                        · linarith only [h921, hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h0, hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h0, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h0, h589, h597, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h0, hc15, hlam, hphi, ht0b, ht5b, p908_1, u0elo0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h1, hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h588, hlam, p908_1]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h591, hlam, p908_1]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h593, hlam, p908_1]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h2, hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h589, hlam, p908_1]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h2, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p749_1, p908_1, u0elo4]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h595, hlam, p908_1]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h3, hlam, p908_0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h590, hlam, p908_1]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h3, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1, u0elo0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [h0, h590, hc14, hlam, hphi, ht0b, ht45, ht5b, p908_1, u0elo0]
                                      · have p908_0 := h908c.1
                                        have p908_1 := h908c.2.1
                                        have p908_2 := h908c.2.2.1
                                        have p908_3 := h908c.2.2.2
                                        linarith only [hlam, p908_0]
                                    · rcases h1bigk with h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p946_1, u0elo0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        rcases p946_3 (m.d 0 1) (by simp) with h949 | h949
                                        · rcases p946_3 (m.d 1 2) (by simp) with h950 | h950
                                          · linarith only [h0, h950, hlam]
                                          · linarith only [h588, h950, hlam]
                                        · linarith only [h949, hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        rcases p946_3 (m.d 0 1) (by simp) with h954 | h954
                                        · rcases p946_3 (m.d 1 2) (by simp) with h955 | h955
                                          · linarith only [h0, h955, hlam]
                                          · linarith only [h589, h955, hlam]
                                        · linarith only [h954, hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        rcases p946_3 (m.d 0 1) (by simp) with h959 | h959
                                        · rcases p946_3 (m.d 1 2) (by simp) with h960 | h960
                                          · linarith only [h0, h960, hlam]
                                          · linarith only [h590, h960, hlam]
                                        · linarith only [h959, hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h0, hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h0, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p946_1, u0elo0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h0, h589, h597, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p946_1, u0elo0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h0, hc15, hlam, hphi, ht0b, ht5b, p946_1, u0elo0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h1, hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h588, hlam, p946_1]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h591, hlam, p946_1]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h593, hlam, p946_1]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h2, hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h589, hlam, p946_1]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h2, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p946_1, u0elo0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h595, hlam, p946_1]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h3, hlam, p946_0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h590, hlam, p946_1]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h3, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p946_1, u0elo0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [h0, h590, hc14, hlam, hphi, ht0b, ht45, ht5b, p946_1, u0elo0]
                                      · have p946_0 := h946c.1
                                        have p946_1 := h946c.2.1
                                        have p946_2 := h946c.2.2.1
                                        have p946_3 := h946c.2.2.2
                                        linarith only [hlam, p946_0]
                                    · linarith only [h603, h7, h907, hc45, hlam, ht01, ht12, ht23, ht34]
                                    · linarith only [h0, h6, h907, hlam, p749_1, u0elo0]
                                    · rcases h1bigk with h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p986_1, u0elo0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        rcases p986_3 (m.d 0 1) (by simp) with h989 | h989
                                        · rcases p986_3 (m.d 1 2) (by simp) with h990 | h990
                                          · linarith only [h0, h990, hlam]
                                          · linarith only [h588, h990, hlam]
                                        · linarith only [h989, hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        rcases p986_3 (m.d 0 1) (by simp) with h994 | h994
                                        · rcases p986_3 (m.d 1 2) (by simp) with h995 | h995
                                          · linarith only [h0, h995, hlam]
                                          · linarith only [h589, h995, hlam]
                                        · linarith only [h994, hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        rcases p986_3 (m.d 0 1) (by simp) with h999 | h999
                                        · rcases p986_3 (m.d 1 2) (by simp) with h1000 | h1000
                                          · linarith only [h0, h1000, hlam]
                                          · linarith only [h1000, h590, hlam]
                                        · linarith only [h999, hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h0, hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h0, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p986_1, u0elo0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h0, hc14, hlam, hphi, ht0b, ht45, ht5b, p986_1, u0elo0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h0, hc15, hlam, hphi, ht0b, ht5b, p986_1, u0elo0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h1, hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h588, hlam, p986_1]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h591, hlam, p986_1]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h593, hlam, p986_1]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h2, hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h589, hlam, p986_1]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h2, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p986_1, u0elo0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h595, hlam, p986_1]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h3, hlam, p986_0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h590, hlam, p986_1]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h3, h588, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p986_1, u0elo0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [h0, h590, hc14, hlam, hphi, ht0b, ht45, ht5b, p986_1, u0elo0]
                                      · have p986_0 := h986c.1
                                        have p986_1 := h986c.2.1
                                        have p986_2 := h986c.2.2.1
                                        have p986_3 := h986c.2.2.2
                                        linarith only [hlam, p986_0]
                                  · linarith only [h301, h906, hlam]
                            · linarith only [h5, h901, hlam]
                          · linarith only [h2, h900, hlam]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [hlam, p749_0]
        · linarith only [h0, h588, h590, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · linarith only [h0, h5, h588, h589, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1030 | h1030
      · linarith only [h0, h1030, h4, h588, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1032 | h1032
        · linarith only [h0, h1032, h4, h588, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1034 | h1034
          · linarith only [h1, h1034, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1036 | h1036
            · linarith only [h1, h1036, h238, h4, h588, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1038 | h1038
              · linarith only [h1038, h2, h301, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1040 | h1040
                · linarith only [h1040, h4, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1042 | h1042
                  · linarith only [h1042, h238, h4, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1044 | h1044
                    · linarith only [h0, h1044, h301, h5, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1046 | h1046
                      · linarith only [h1046, h301, h4, h588, h7, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1046, h4, h588, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h238 | h238
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x0_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h238
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x0_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h238

end R2N4
