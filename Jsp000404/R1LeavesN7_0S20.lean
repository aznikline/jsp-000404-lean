import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S17
import Jsp000404.R1LeavesN7_0S18
import Jsp000404.R1LeavesN7_0S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x23 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 5) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 5) ∧ (m.d 1 4) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 4) ≤ z)))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  rcases p9633_3 (m.d 0 1) (by simp) with h10311 | h10311
  · rcases p9633_3 (m.d 1 2) (by simp) with h10312 | h10312
    · rcases p9633_3 (m.d 1 3) (by simp) with h10313 | h10313
      · linarith only [h10313, h9619, hlam]
      · rcases p9633_3 (m.d 1 4) (by simp) with h10315 | h10315
        · linarith only [h10315, h9623, hlam]
        · rcases p9633_3 (m.d 1 5) (by simp) with h10317 | h10317
          · rcases h1emax with h10318 | h10318 | h10318 | h10318 | h10318
            · linarith only [h0, h10318, h9270, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h10318, h9269, h9270, h9625, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9633_1]
            · rcases h2bigk with h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c | h10321c
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h0, h9269, h9270, h9625, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10321_1, p9633_1]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h4, h8, h9269, h9619, h9625, hlam, p10321_2, p9633_1]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h4, h8, h9269, h9619, hlam, p10321_2, p9633_1]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                rcases p10321_3 (m.d 0 2) (by simp) with h10326 | h10326
                · rcases p10321_3 (m.d 1 2) (by simp) with h10327 | h10327
                  · linarith only [h0, h10327, hlam]
                  · linarith only [h10327, h9270, hlam]
                · linarith only [h10326, hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h0, hlam, p10321_1]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                rcases p10321_3 (m.d 0 2) (by simp) with h10333 | h10333
                · rcases p10321_3 (m.d 1 2) (by simp) with h10334 | h10334
                  · rcases p10321_3 (m.d 2 3) (by simp) with h10335 | h10335
                    · linarith only [h10335, hlam, p10321_0]
                    · rcases p10321_3 (m.d 2 4) (by simp) with h10337 | h10337
                      · linarith only [h10337, h9269, hlam]
                      · linarith only [h10337, h9625, hlam]
                  · linarith only [h10334, hlam, p10321_0]
                · linarith only [h10333, h4, hlam]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                rcases p10321_3 (m.d 0 2) (by simp) with h10342 | h10342
                · rcases p10321_3 (m.d 1 2) (by simp) with h10343 | h10343
                  · rcases p10321_3 (m.d 2 3) (by simp) with h10344 | h10344
                    · linarith only [h10344, h9268, hlam]
                    · rcases p10321_3 (m.d 2 4) (by simp) with h10346 | h10346
                      · linarith only [h10346, hlam, p10321_0]
                      · rcases p10321_3 (m.d 2 5) (by simp) with h10348 | h10348
                        · linarith only [h10348, h9270, hlam]
                        · linarith only [h10348, h9629, hlam]
                  · linarith only [h10343, hlam, p10321_0]
                · linarith only [h10342, h5, hlam]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                rcases p10321_3 (m.d 0 2) (by simp) with h10353 | h10353
                · rcases p10321_3 (m.d 1 2) (by simp) with h10354 | h10354
                  · rcases p10321_3 (m.d 2 3) (by simp) with h10355 | h10355
                    · linarith only [h10355, h9268, hlam]
                    · rcases p10321_3 (m.d 2 4) (by simp) with h10357 | h10357
                      · linarith only [h10357, h9269, hlam]
                      · rcases p10321_3 (m.d 2 5) (by simp) with h10359 | h10359
                        · linarith only [h10359, hlam, p10321_0]
                        · rcases h4bigk with h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c | h10361c
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9, h9269, h9625, hc23, hc45, hlam, hphi, ht34, p10361_1]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9, h9625, hc23, hc45, hlam, hphi, ht34, p10361_1]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10361_1]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9, hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h2, hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h4, h8, h9619, h9625, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10361_1, p9633_1]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9271, hlam, p10361_1]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9623, hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h5, hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9269, hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9625, hlam, p10361_1]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9629, hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h7, hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h7, h9, hc14, hc45, hlam, hphi, p10361_1]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h7, h9, h9625, hc23, hc45, hlam, hphi, ht34, p10361_1]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9631, hlam, p10361_0]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h7, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10361_1]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            rcases p10361_3 (m.d 0 4) (by simp) with h10383 | h10383
                            · linarith only [h10383, h9, hlam]
                            · linarith only [h10383, h2, hlam]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            rcases p10361_3 (m.d 0 4) (by simp) with h10386 | h10386
                            · linarith only [h10386, h9, hlam]
                            · linarith only [h10386, h5, hlam]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10361_1]
                          · have p10361_0 := h10361c.1
                            have p10361_1 := h10361c.2.1
                            have p10361_2 := h10361c.2.2.1
                            have p10361_3 := h10361c.2.2.2
                            linarith only [hlam, p10361_0]
                  · linarith only [h10354, hlam, p10321_0]
                · linarith only [h10353, h6, hlam]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h4, hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h9268, hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h9625, hlam, p10321_1]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h9627, hlam, p10321_1]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h5, hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h9269, hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h2, h9, h9269, hc23, hc45, hlam, hphi, ht34, p10321_1]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h9629, hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h6, hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h9270, hlam, p10321_0]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h0, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10321_1]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [h0, h9270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p10321_1]
              · have p10321_0 := h10321c.1
                have p10321_1 := h10321c.2.1
                have p10321_2 := h10321c.2.2.1
                have p10321_3 := h10321c.2.2.2
                linarith only [hlam, p10321_0]
            · rcases h2bigk with h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c | h10408c
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h0, h9270, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p10408_1, p9633_1]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h4, h8, h9269, h9619, h9625, hlam, p10408_2, p9633_1]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h4, h8, h9269, h9619, hlam, p10408_2, p9633_1]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                rcases p10408_3 (m.d 0 2) (by simp) with h10413 | h10413
                · rcases p10408_3 (m.d 1 2) (by simp) with h10414 | h10414
                  · linarith only [h0, h10414, hlam]
                  · linarith only [h10414, h9270, hlam]
                · linarith only [h10413, hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h0, hlam, p10408_1]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                rcases p10408_3 (m.d 0 2) (by simp) with h10420 | h10420
                · rcases p10408_3 (m.d 1 2) (by simp) with h10421 | h10421
                  · rcases p10408_3 (m.d 2 3) (by simp) with h10422 | h10422
                    · linarith only [h10422, hlam, p10408_0]
                    · rcases p10408_3 (m.d 2 4) (by simp) with h10424 | h10424
                      · linarith only [h10424, h9269, hlam]
                      · linarith only [h10424, h9625, hlam]
                  · linarith only [h10421, hlam, p10408_0]
                · linarith only [h10420, h4, hlam]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                rcases p10408_3 (m.d 0 2) (by simp) with h10429 | h10429
                · rcases p10408_3 (m.d 1 2) (by simp) with h10430 | h10430
                  · rcases p10408_3 (m.d 2 3) (by simp) with h10431 | h10431
                    · linarith only [h10431, h9268, hlam]
                    · rcases p10408_3 (m.d 2 4) (by simp) with h10433 | h10433
                      · linarith only [h10433, hlam, p10408_0]
                      · rcases p10408_3 (m.d 2 5) (by simp) with h10435 | h10435
                        · linarith only [h10435, h9270, hlam]
                        · linarith only [h10435, h9629, hlam]
                  · linarith only [h10430, hlam, p10408_0]
                · linarith only [h10429, h5, hlam]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                rcases p10408_3 (m.d 0 2) (by simp) with h10440 | h10440
                · rcases p10408_3 (m.d 1 2) (by simp) with h10441 | h10441
                  · rcases p10408_3 (m.d 2 3) (by simp) with h10442 | h10442
                    · linarith only [h10442, h9268, hlam]
                    · rcases p10408_3 (m.d 2 4) (by simp) with h10444 | h10444
                      · linarith only [h10444, h9269, hlam]
                      · rcases p10408_3 (m.d 2 5) (by simp) with h10446 | h10446
                        · linarith only [h10446, hlam, p10408_0]
                        · rcases h4bigk with h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c | h10448c
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9, hc14, hc45, hlam, hphi, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9, h9625, hc23, hc45, hlam, hphi, ht34, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9, hc34, hc45, hlam, hphi, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h2, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h0, h4, h8, h9619, h9625, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10448_1, p9633_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9271, hlam, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9623, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h5, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9269, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9625, hlam, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9629, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h7, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h7, h9, hc14, hc45, hlam, hphi, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h7, h9, h9625, hc23, hc45, hlam, hphi, ht34, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9631, hlam, p10448_0]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h7, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            rcases p10448_3 (m.d 0 4) (by simp) with h10470 | h10470
                            · linarith only [h10470, h9, hlam]
                            · linarith only [h10470, h2, hlam]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            rcases p10448_3 (m.d 0 4) (by simp) with h10473 | h10473
                            · linarith only [h10473, h9, hlam]
                            · linarith only [h10473, h5, hlam]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10448_1]
                          · have p10448_0 := h10448c.1
                            have p10448_1 := h10448c.2.1
                            have p10448_2 := h10448c.2.2.1
                            have p10448_3 := h10448c.2.2.2
                            linarith only [hlam, p10448_0]
                  · linarith only [h10441, hlam, p10408_0]
                · linarith only [h10440, h6, hlam]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h4, hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h9268, hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h9625, hlam, p10408_1]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h9627, hlam, p10408_1]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h5, hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h9269, hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h2, h9, h9269, hc23, hc45, hlam, hphi, ht34, p10408_1]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h9629, hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h6, hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h9270, hlam, p10408_0]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h0, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10408_1]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [h0, h9270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p10408_1]
              · have p10408_0 := h10408c.1
                have p10408_1 := h10408c.2.1
                have p10408_2 := h10408c.2.2.1
                have p10408_3 := h10408c.2.2.2
                linarith only [hlam, p10408_0]
            · linarith only [h10318, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p9633_1]
          · linarith only [h10317, h9623, hlam]
    · linarith only [h10312, h9269, hlam]
  · linarith only [h10311, h2, hlam]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x24 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 5) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 5) ∧ (m.d 1 5) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 5) ≤ z)))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases h1bigk with h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x2 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x3 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x4 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x5 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x6 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x7 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x8 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x9 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x10 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x11 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x12 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x13 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x14 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x15 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x16 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x17 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x18 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x19 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x20 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x21 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x22 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x23 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x24 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631 h9633c

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 3 4 5 (by decide) (by decide) with h9631 | h9631
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629 h9631

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 2 4 5 (by decide) (by decide) with h9629 | h9629
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627 h9629

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 2 3 5 (by decide) (by decide) with h9627 | h9627
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625 h9627

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 2 3 4 (by decide) (by decide) with h9625 | h9625
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623 h9625

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 4 5 (by decide) (by decide) with h9623 | h9623
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619 h9623

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h9619 | h9619
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271 h9619

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h9271 | h9271
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270 h9271

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h10500 | h10500
  · rcases m.htr 1 3 5 (by decide) (by decide) with h10501 | h10501
    · linarith only [h10501, h9268, h9270, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h10503 | h10503
      · linarith only [h10503, h2, h9, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h10505 | h10505
        · linarith only [h0, h10505, h6, h9268, h9270, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h10500, h10505, h6, h9268, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h10508 | h10508
    · linarith only [h10500, h10508, h7, h9, h9268, h9270, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h10510 | h10510
      · linarith only [h0, h10500, h10510, h7, h9, h9269, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h10512 | h10512
        · linarith only [h10500, h10512, h9268, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h10514 | h10514
          · linarith only [h0, h10508, h10514, h6, h9268, h9270, hc01, hc15, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h10516 | h10516
            · linarith only [h10500, h10516, h7, h9, h9269, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h10518 | h10518
              · linarith only [h10514, h10518, h7, h8, h9, h9269, h9270, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h1bigk with h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  rcases p10520_3 (m.d 0 1) (by simp) with h10522 | h10522
                  · rcases p10520_3 (m.d 1 2) (by simp) with h10523 | h10523
                    · linarith only [h10523, hlam, p10520_0]
                    · rcases p10520_3 (m.d 1 3) (by simp) with h10525 | h10525
                      · linarith only [h1, h10525, hlam]
                      · rcases p10520_3 (m.d 1 4) (by simp) with h10527 | h10527
                        · linarith only [h10527, h2, hlam]
                        · rcases p10520_3 (m.d 1 5) (by simp) with h10529 | h10529
                          · linarith only [h10529, h3, hlam]
                          · linarith only [h10529, h9270, hlam]
                  · linarith only [h10522, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  rcases p10520_3 (m.d 0 1) (by simp) with h10533 | h10533
                  · rcases p10520_3 (m.d 1 2) (by simp) with h10534 | h10534
                    · linarith only [h0, h10534, hlam]
                    · linarith only [h10534, h9268, hlam]
                  · linarith only [h10533, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  rcases p10520_3 (m.d 0 1) (by simp) with h10538 | h10538
                  · rcases p10520_3 (m.d 1 2) (by simp) with h10539 | h10539
                    · linarith only [h0, h10539, hlam]
                    · linarith only [h10539, h9269, hlam]
                  · linarith only [h10538, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  rcases p10520_3 (m.d 0 1) (by simp) with h10543 | h10543
                  · rcases p10520_3 (m.d 1 2) (by simp) with h10544 | h10544
                    · linarith only [h0, h10544, hlam]
                    · rcases p10520_3 (m.d 1 3) (by simp) with h10546 | h10546
                      · linarith only [h1, h10546, hlam]
                      · rcases p10520_3 (m.d 1 4) (by simp) with h10548 | h10548
                        · linarith only [h10548, h2, hlam]
                        · rcases p10520_3 (m.d 1 5) (by simp) with h10550 | h10550
                          · linarith only [h10550, hlam, p10520_0]
                          · rcases h1emax with h10552 | h10552 | h10552 | h10552 | h10552
                            · linarith only [h0, h10512, h10552, h9269, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases h2bigk with h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c | h10554c
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                rcases p10554_3 (m.d 0 2) (by simp) with h10556 | h10556
                                · rcases p10554_3 (m.d 1 2) (by simp) with h10557 | h10557
                                  · linarith only [h0, h10557, hlam]
                                  · rcases p10554_3 (m.d 2 3) (by simp) with h10559 | h10559
                                    · linarith only [h10559, h4, hlam]
                                    · rcases p10554_3 (m.d 2 4) (by simp) with h10561 | h10561
                                      · linarith only [h10561, h5, hlam]
                                      · rcases p10554_3 (m.d 2 5) (by simp) with h10563 | h10563
                                        · linarith only [h10563, h6, hlam]
                                        · linarith only [h10563, h9270, hlam]
                                · linarith only [h0, h10556, hlam]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h10512, h10514, h4, h8, h9269, h9270, hlam, p10554_2]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h10514, h4, h8, h9269, h9270, hlam, p10554_2]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h0, h10512, h9269, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10554_1]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h0, hlam, p10554_1]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h10514, h8, h9270, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10554_1]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h0, h10512, h10514, h4, h8, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10554_1]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h9270, hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h4, hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h9268, hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h10512, hlam, p10554_1]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h10514, hlam, p10554_1]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h5, hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h9269, hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h5, h9, hc23, hc45, hlam, hphi, ht34, p10554_1]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h10516, hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h6, hlam, p10554_0]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [h0, h10514, h4, h8, h9268, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10554_1]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                rcases p10554_3 (m.d 0 2) (by simp) with h10587 | h10587
                                · rcases p10554_3 (m.d 1 2) (by simp) with h10588 | h10588
                                  · linarith only [h10588, h9270, hlam]
                                  · linarith only [h10588, h9268, hlam]
                                · linarith only [h10587, h4, hlam]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                rcases p10554_3 (m.d 0 2) (by simp) with h10592 | h10592
                                · rcases p10554_3 (m.d 1 2) (by simp) with h10593 | h10593
                                  · linarith only [h10593, h9270, hlam]
                                  · linarith only [h10593, h9269, hlam]
                                · linarith only [h10592, h5, hlam]
                              · have p10554_0 := h10554c.1
                                have p10554_1 := h10554c.2.1
                                have p10554_2 := h10554c.2.2.1
                                have p10554_3 := h10554c.2.2.2
                                linarith only [hlam, p10554_0]
                            · rcases h2bigk with h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                rcases p10598_3 (m.d 0 2) (by simp) with h10600 | h10600
                                · rcases p10598_3 (m.d 1 2) (by simp) with h10601 | h10601
                                  · linarith only [h0, h10601, hlam]
                                  · rcases p10598_3 (m.d 2 3) (by simp) with h10603 | h10603
                                    · linarith only [h10603, h4, hlam]
                                    · rcases p10598_3 (m.d 2 4) (by simp) with h10605 | h10605
                                      · linarith only [h10605, h5, hlam]
                                      · rcases p10598_3 (m.d 2 5) (by simp) with h10607 | h10607
                                        · linarith only [h10607, h6, hlam]
                                        · linarith only [h10607, h9270, hlam]
                                · linarith only [h0, h10600, hlam]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h10512, h10514, h4, h8, h9269, h9270, hlam, p10598_2]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h10514, h4, h8, h9269, h9270, hlam, p10598_2]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h10512, h9269, h9270, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10598_1]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h0, hlam, p10598_1]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h10514, h8, h9270, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10598_1]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h0, h10512, h10514, h4, h8, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10598_1]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h9270, hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h4, hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h9268, hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h10512, hlam, p10598_1]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h10514, hlam, p10598_1]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h5, hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h9269, hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h5, h9, hc23, hc45, hlam, hphi, ht34, p10598_1]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h10516, hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h6, hlam, p10598_0]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [h0, h10514, h4, h8, h9268, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10598_1]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                rcases p10598_3 (m.d 0 2) (by simp) with h10631 | h10631
                                · rcases p10598_3 (m.d 1 2) (by simp) with h10632 | h10632
                                  · linarith only [h10632, h9270, hlam]
                                  · linarith only [h10632, h9268, hlam]
                                · linarith only [h10631, h4, hlam]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                rcases p10598_3 (m.d 0 2) (by simp) with h10636 | h10636
                                · rcases p10598_3 (m.d 1 2) (by simp) with h10637 | h10637
                                  · linarith only [h10637, h9270, hlam]
                                  · linarith only [h10637, h9269, hlam]
                                · linarith only [h10636, h5, hlam]
                              · have p10598_0 := h10598c.1
                                have p10598_1 := h10598c.2.1
                                have p10598_2 := h10598c.2.2.1
                                have p10598_3 := h10598c.2.2.2
                                linarith only [hlam, p10598_0]
                            · rcases h2bigk with h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c | h10642c
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                rcases p10642_3 (m.d 0 2) (by simp) with h10644 | h10644
                                · rcases p10642_3 (m.d 1 2) (by simp) with h10645 | h10645
                                  · linarith only [h0, h10645, hlam]
                                  · rcases p10642_3 (m.d 2 3) (by simp) with h10647 | h10647
                                    · linarith only [h10647, h4, hlam]
                                    · rcases p10642_3 (m.d 2 4) (by simp) with h10649 | h10649
                                      · linarith only [h10649, h5, hlam]
                                      · rcases p10642_3 (m.d 2 5) (by simp) with h10651 | h10651
                                        · linarith only [h10651, h6, hlam]
                                        · linarith only [h10651, h9270, hlam]
                                · linarith only [h0, h10644, hlam]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h10512, h10514, h4, h8, h9269, h9270, hlam, p10642_2]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h10514, h4, h8, h9269, h9270, hlam, p10642_2]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h10512, h9269, h9270, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10642_1]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h0, hlam, p10642_1]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h10514, h8, h9270, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10642_1]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h0, h10512, h10514, h4, h8, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10642_1]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h9270, hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h4, hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h9268, hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h10512, hlam, p10642_1]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h10514, hlam, p10642_1]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h5, hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h9269, hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h5, h9, hc23, hc45, hlam, hphi, ht34, p10642_1]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h10516, hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h6, hlam, p10642_0]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [h0, h10514, h4, h8, h9268, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10642_1]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                rcases p10642_3 (m.d 0 2) (by simp) with h10675 | h10675
                                · rcases p10642_3 (m.d 1 2) (by simp) with h10676 | h10676
                                  · linarith only [h10676, h9270, hlam]
                                  · linarith only [h10676, h9268, hlam]
                                · linarith only [h10675, h4, hlam]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                rcases p10642_3 (m.d 0 2) (by simp) with h10680 | h10680
                                · rcases p10642_3 (m.d 1 2) (by simp) with h10681 | h10681
                                  · linarith only [h10681, h9270, hlam]
                                  · linarith only [h10681, h9269, hlam]
                                · linarith only [h10680, h5, hlam]
                              · have p10642_0 := h10642c.1
                                have p10642_1 := h10642c.2.1
                                have p10642_2 := h10642c.2.2.1
                                have p10642_3 := h10642c.2.2.2
                                linarith only [hlam, p10642_0]
                            · rcases h2bigk with h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c | h10686c
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                rcases p10686_3 (m.d 0 2) (by simp) with h10688 | h10688
                                · rcases p10686_3 (m.d 1 2) (by simp) with h10689 | h10689
                                  · linarith only [h0, h10689, hlam]
                                  · rcases p10686_3 (m.d 2 3) (by simp) with h10691 | h10691
                                    · linarith only [h10691, h4, hlam]
                                    · rcases p10686_3 (m.d 2 4) (by simp) with h10693 | h10693
                                      · linarith only [h10693, h5, hlam]
                                      · rcases p10686_3 (m.d 2 5) (by simp) with h10695 | h10695
                                        · linarith only [h10695, h6, hlam]
                                        · linarith only [h10695, h9270, hlam]
                                · linarith only [h0, h10688, hlam]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h10512, h10514, h4, h8, h9269, h9270, hlam, p10686_2]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h10514, h4, h8, h9269, h9270, hlam, p10686_2]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h10512, h9269, h9270, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10686_1]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h0, hlam, p10686_1]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h10514, h8, h9270, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10686_1]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h0, h10512, h10514, h4, h8, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10686_1]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h9270, hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h4, hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h9268, hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h10512, hlam, p10686_1]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h10514, hlam, p10686_1]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h5, hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h9269, hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h5, h9, hc23, hc45, hlam, hphi, ht34, p10686_1]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h10516, hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h6, hlam, p10686_0]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [h0, h10514, h4, h8, h9268, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10686_1]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                rcases p10686_3 (m.d 0 2) (by simp) with h10719 | h10719
                                · rcases p10686_3 (m.d 1 2) (by simp) with h10720 | h10720
                                  · linarith only [h10720, h9270, hlam]
                                  · linarith only [h10720, h9268, hlam]
                                · linarith only [h10719, h4, hlam]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                rcases p10686_3 (m.d 0 2) (by simp) with h10724 | h10724
                                · rcases p10686_3 (m.d 1 2) (by simp) with h10725 | h10725
                                  · linarith only [h10725, h9270, hlam]
                                  · linarith only [h10725, h9269, hlam]
                                · linarith only [h10724, h5, hlam]
                              · have p10686_0 := h10686c.1
                                have p10686_1 := h10686c.2.1
                                have p10686_2 := h10686c.2.2.1
                                have p10686_3 := h10686c.2.2.2
                                linarith only [hlam, p10686_0]
                  · linarith only [h10543, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h0, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h0, h10514, h4, h8, h9268, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10520_1]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h0, h10514, h4, h8, h9270, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p10520_1]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h9270, hlam, p10520_1]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h1, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h9268, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h10500, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h10508, hlam, p10520_1]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h2, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h9269, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h2, h9, h9268, hc23, hc45, hlam, hphi, ht34, p10520_1]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h10510, hlam, p10520_1]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h3, hlam, p10520_0]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [h3, h9268, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10520_1]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  rcases p10520_3 (m.d 0 1) (by simp) with h10748 | h10748
                  · rcases p10520_3 (m.d 1 2) (by simp) with h10749 | h10749
                    · linarith only [h10749, h9270, hlam]
                    · linarith only [h10749, h9268, hlam]
                  · linarith only [h1, h10748, hlam]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  rcases p10520_3 (m.d 0 1) (by simp) with h10753 | h10753
                  · rcases p10520_3 (m.d 1 2) (by simp) with h10754 | h10754
                    · linarith only [h10754, h9270, hlam]
                    · linarith only [h10754, h9269, hlam]
                  · linarith only [h10753, h2, hlam]
                · have p10520_0 := h10520c.1
                  have p10520_1 := h10520c.2.1
                  have p10520_2 := h10520c.2.2.1
                  have p10520_3 := h10520c.2.2.2
                  linarith only [hlam, p10520_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 5 (by decide) (by decide) with h9270 | h9270
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269 h9270

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  linarith only [h5, h9, h9268, h9269, hc23, hc45, hlam, hphi, ht34]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 4 (by decide) (by decide) with h9269 | h9269
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h9269

end R2N4
