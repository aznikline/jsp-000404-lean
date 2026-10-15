import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S42
import Jsp000404.R1LeavesN7_0S45

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  rcases m.htr 1 3 5 (by decide) (by decide) with h28285 | h28285
  · rcases m.htr 1 4 5 (by decide) (by decide) with h28286 | h28286
    · linarith only [h2, h23339, h28286, hlam]
    · linarith only [h26251, h28285, h28286, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h28289 | h28289
    · linarith only [h2, h23339, h28289, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h28291 | h28291
      · rcases m.htr 2 3 5 (by decide) (by decide) with h28292 | h28292
        · rcases m.htr 2 4 5 (by decide) (by decide) with h28293 | h28293
          · linarith only [h23337, h23339, h26245, h26251, h28293, hc12, hc24, hlam, hphi]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h28295 | h28295
            · linarith only [h1, h19744, h23337, h28293, h28295, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c | h28297c
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                rcases p28297_3 (m.d 0 1) (by simp) with h28299 | h28299
                · rcases p28297_3 (m.d 1 2) (by simp) with h28300 | h28300
                  · linarith only [h28300, hlam, p28297_0]
                  · rcases p28297_3 (m.d 1 3) (by simp) with h28302 | h28302
                    · linarith only [h1, h28302, hlam]
                    · linarith only [h26245, h28302, hlam]
                · linarith only [h28299, hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                rcases p28297_3 (m.d 0 1) (by simp) with h28306 | h28306
                · rcases p28297_3 (m.d 1 2) (by simp) with h28307 | h28307
                  · linarith only [h0, h28307, hlam]
                  · rcases p28297_3 (m.d 1 3) (by simp) with h28309 | h28309
                    · linarith only [h28309, hlam, p28297_0]
                    · rcases p28297_3 (m.d 1 4) (by simp) with h28311 | h28311
                      · linarith only [h2, h28311, hlam]
                      · linarith only [h26251, h28311, hlam]
                · linarith only [h28306, hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                rcases p28297_3 (m.d 0 1) (by simp) with h28315 | h28315
                · rcases p28297_3 (m.d 1 2) (by simp) with h28316 | h28316
                  · linarith only [h0, h28316, hlam]
                  · rcases p28297_3 (m.d 1 3) (by simp) with h28318 | h28318
                    · linarith only [h1, h28318, hlam]
                    · rcases p28297_3 (m.d 1 4) (by simp) with h28320 | h28320
                      · linarith only [h28320, hlam, p28297_0]
                      · rcases p28297_3 (m.d 1 5) (by simp) with h28322 | h28322
                        · linarith only [h28322, h3, hlam]
                        · linarith only [h28289, h28322, hlam]
                · linarith only [h28315, hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                rcases p28297_3 (m.d 0 1) (by simp) with h28326 | h28326
                · rcases p28297_3 (m.d 1 2) (by simp) with h28327 | h28327
                  · linarith only [h0, h28327, hlam]
                  · rcases p28297_3 (m.d 1 3) (by simp) with h28329 | h28329
                    · linarith only [h1, h28329, hlam]
                    · rcases p28297_3 (m.d 1 4) (by simp) with h28331 | h28331
                      · linarith only [h2, h28331, hlam]
                      · rcases p28297_3 (m.d 1 5) (by simp) with h28333 | h28333
                        · linarith only [h28333, hlam, p28297_0]
                        · rcases h1emax with h28335 | h28335 | h28335 | h28335 | h28335
                          · linarith only [h1, h23338, h26251, h28295, h28335, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases h2bigk with h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c | h28337c
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h4, hc12, hc23, hlam, hphi, p28337_1]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h4, hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h19744, hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h22010, hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h0, hlam, p28337_1]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h26245, hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h26247, hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h26249, hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              rcases p28337_3 (m.d 0 2) (by simp) with h28348 | h28348
                              · linarith only [h28348, hlam, p28337_0]
                              · rcases p28337_3 (m.d 1 2) (by simp) with h28350 | h28350
                                · linarith only [h26245, h28350, hlam]
                                · rcases p28337_3 (m.d 2 3) (by simp) with h28352 | h28352
                                  · rcases p28337_3 (m.d 2 4) (by simp) with h28353 | h28353
                                    · linarith only [h28291, h28353, hlam]
                                    · linarith only [h19744, h28353, hlam]
                                  · linarith only [h28352, hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              rcases p28337_3 (m.d 0 2) (by simp) with h28357 | h28357
                              · linarith only [h28357, h4, hlam]
                              · linarith only [h0, h28357, hlam]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h19744, h23337, h26245, h26251, hc12, hc23, hlam, hphi, p28337_1]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h22010, hc02, hc23, hlam, hphi, p28337_1]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h0, h28293, hc12, hc45, hlam, hphi, ht23, ht34, p28337_1]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h28293, hc12, hc45, hlam, hphi, ht23, ht34, p28337_1]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h28291, hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h28293, hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              rcases p28337_3 (m.d 0 2) (by simp) with h28368 | h28368
                              · linarith only [h28368, hlam, p28337_0]
                              · rcases p28337_3 (m.d 1 2) (by simp) with h28370 | h28370
                                · linarith only [h26249, h28370, hlam]
                                · rcases p28337_3 (m.d 2 3) (by simp) with h28372 | h28372
                                  · rcases p28337_3 (m.d 2 4) (by simp) with h28373 | h28373
                                    · linarith only [h28293, h28373, hlam]
                                    · linarith only [h19744, h28373, hlam]
                                  · linarith only [h28372, h4, hlam]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              rcases p28337_3 (m.d 0 2) (by simp) with h28377 | h28377
                              · linarith only [h22010, h28377, hlam]
                              · linarith only [h0, h28377, hlam]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h28292, hlam, p28337_0]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [h0, h19744, hc12, hc25, hlam, hphi, p28337_1]
                            · have p28337_0 := h28337c.1
                              have p28337_1 := h28337c.2.1
                              have p28337_2 := h28337c.2.2.1
                              have p28337_3 := h28337c.2.2.2
                              linarith only [hlam, p28337_0]
                          · rcases h2bigk with h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c | h28383c
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h4, hc12, hc23, hlam, hphi, p28383_1]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h4, hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h19744, hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h22010, hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h0, hlam, p28383_1]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h26245, hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h26247, hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h26249, hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              rcases p28383_3 (m.d 0 2) (by simp) with h28394 | h28394
                              · linarith only [h28394, hlam, p28383_0]
                              · rcases p28383_3 (m.d 1 2) (by simp) with h28396 | h28396
                                · linarith only [h26245, h28396, hlam]
                                · rcases p28383_3 (m.d 2 3) (by simp) with h28398 | h28398
                                  · rcases p28383_3 (m.d 2 4) (by simp) with h28399 | h28399
                                    · linarith only [h28291, h28399, hlam]
                                    · linarith only [h19744, h28399, hlam]
                                  · linarith only [h28398, hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              rcases p28383_3 (m.d 0 2) (by simp) with h28403 | h28403
                              · linarith only [h28403, h4, hlam]
                              · linarith only [h0, h28403, hlam]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h19744, h23337, h26245, h26251, hc12, hc23, hlam, hphi, p28383_1]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h22010, hc02, hc23, hlam, hphi, p28383_1]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h0, h28293, hc12, hc45, hlam, hphi, ht23, ht34, p28383_1]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h28293, hc12, hc45, hlam, hphi, ht23, ht34, p28383_1]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h28291, hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h28293, hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              rcases p28383_3 (m.d 0 2) (by simp) with h28414 | h28414
                              · linarith only [h28414, hlam, p28383_0]
                              · rcases p28383_3 (m.d 1 2) (by simp) with h28416 | h28416
                                · linarith only [h26249, h28416, hlam]
                                · rcases p28383_3 (m.d 2 3) (by simp) with h28418 | h28418
                                  · rcases p28383_3 (m.d 2 4) (by simp) with h28419 | h28419
                                    · linarith only [h28293, h28419, hlam]
                                    · linarith only [h19744, h28419, hlam]
                                  · linarith only [h28418, h4, hlam]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              rcases p28383_3 (m.d 0 2) (by simp) with h28423 | h28423
                              · linarith only [h22010, h28423, hlam]
                              · linarith only [h0, h28423, hlam]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h28292, hlam, p28383_0]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [h0, h19744, hc12, hc25, hlam, hphi, p28383_1]
                            · have p28383_0 := h28383c.1
                              have p28383_1 := h28383c.2.1
                              have p28383_2 := h28383c.2.2.1
                              have p28383_3 := h28383c.2.2.2
                              linarith only [hlam, p28383_0]
                          · rcases h2bigk with h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c | h28429c
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h4, hc12, hc23, hlam, hphi, p28429_1]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h4, hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h19744, hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h22010, hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h0, hlam, p28429_1]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h26245, hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h26247, hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h26249, hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              rcases p28429_3 (m.d 0 2) (by simp) with h28440 | h28440
                              · linarith only [h28440, hlam, p28429_0]
                              · rcases p28429_3 (m.d 1 2) (by simp) with h28442 | h28442
                                · linarith only [h26245, h28442, hlam]
                                · rcases p28429_3 (m.d 2 3) (by simp) with h28444 | h28444
                                  · rcases p28429_3 (m.d 2 4) (by simp) with h28445 | h28445
                                    · linarith only [h28291, h28445, hlam]
                                    · linarith only [h19744, h28445, hlam]
                                  · linarith only [h28444, hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              rcases p28429_3 (m.d 0 2) (by simp) with h28449 | h28449
                              · linarith only [h28449, h4, hlam]
                              · linarith only [h0, h28449, hlam]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h19744, h23337, h26245, h26251, hc12, hc23, hlam, hphi, p28429_1]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h22010, hc02, hc23, hlam, hphi, p28429_1]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h0, h28293, hc12, hc45, hlam, hphi, ht23, ht34, p28429_1]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h28293, hc12, hc45, hlam, hphi, ht23, ht34, p28429_1]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h28291, hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h28293, hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              rcases p28429_3 (m.d 0 2) (by simp) with h28460 | h28460
                              · linarith only [h28460, hlam, p28429_0]
                              · rcases p28429_3 (m.d 1 2) (by simp) with h28462 | h28462
                                · linarith only [h26249, h28462, hlam]
                                · rcases p28429_3 (m.d 2 3) (by simp) with h28464 | h28464
                                  · rcases p28429_3 (m.d 2 4) (by simp) with h28465 | h28465
                                    · linarith only [h28293, h28465, hlam]
                                    · linarith only [h19744, h28465, hlam]
                                  · linarith only [h28464, h4, hlam]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              rcases p28429_3 (m.d 0 2) (by simp) with h28469 | h28469
                              · linarith only [h22010, h28469, hlam]
                              · linarith only [h0, h28469, hlam]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h28292, hlam, p28429_0]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [h0, h19744, hc12, hc25, hlam, hphi, p28429_1]
                            · have p28429_0 := h28429c.1
                              have p28429_1 := h28429c.2.1
                              have p28429_2 := h28429c.2.2.1
                              have p28429_3 := h28429c.2.2.2
                              linarith only [hlam, p28429_0]
                          · rcases h2bigk with h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c | h28475c
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h4, hc12, hc23, hlam, hphi, p28475_1]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h4, hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h19744, hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h22010, hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h0, hlam, p28475_1]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h26245, hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h26247, hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h26249, hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              rcases p28475_3 (m.d 0 2) (by simp) with h28486 | h28486
                              · linarith only [h28486, hlam, p28475_0]
                              · rcases p28475_3 (m.d 1 2) (by simp) with h28488 | h28488
                                · linarith only [h26245, h28488, hlam]
                                · rcases p28475_3 (m.d 2 3) (by simp) with h28490 | h28490
                                  · rcases p28475_3 (m.d 2 4) (by simp) with h28491 | h28491
                                    · linarith only [h28291, h28491, hlam]
                                    · linarith only [h19744, h28491, hlam]
                                  · linarith only [h28490, hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              rcases p28475_3 (m.d 0 2) (by simp) with h28495 | h28495
                              · linarith only [h28495, h4, hlam]
                              · linarith only [h0, h28495, hlam]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h19744, h23337, h26245, h26251, hc12, hc23, hlam, hphi, p28475_1]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h22010, hc02, hc23, hlam, hphi, p28475_1]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h0, h28293, hc12, hc45, hlam, hphi, ht23, ht34, p28475_1]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h28293, hc12, hc45, hlam, hphi, ht23, ht34, p28475_1]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h28291, hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h28293, hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              rcases p28475_3 (m.d 0 2) (by simp) with h28506 | h28506
                              · linarith only [h28506, hlam, p28475_0]
                              · rcases p28475_3 (m.d 1 2) (by simp) with h28508 | h28508
                                · linarith only [h26249, h28508, hlam]
                                · rcases p28475_3 (m.d 2 3) (by simp) with h28510 | h28510
                                  · rcases p28475_3 (m.d 2 4) (by simp) with h28511 | h28511
                                    · linarith only [h28293, h28511, hlam]
                                    · linarith only [h19744, h28511, hlam]
                                  · linarith only [h28510, h4, hlam]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              rcases p28475_3 (m.d 0 2) (by simp) with h28515 | h28515
                              · linarith only [h22010, h28515, hlam]
                              · linarith only [h0, h28515, hlam]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h28292, hlam, p28475_0]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [h0, h19744, hc12, hc25, hlam, hphi, p28475_1]
                            · have p28475_0 := h28475c.1
                              have p28475_1 := h28475c.2.1
                              have p28475_2 := h28475c.2.2.1
                              have p28475_3 := h28475c.2.2.2
                              linarith only [hlam, p28475_0]
                · linarith only [h28326, hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h0, hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h26245, hlam, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h26247, hlam, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h26249, hlam, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h1, hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h1, h23338, h26251, h28295, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h26251, hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h28285, hlam, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h2, hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h2, h23339, hc12, hc45, hlam, hphi, ht23, ht34, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h23337, h23339, h26251, hc13, hc45, hlam, hphi, ht34, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h28289, hlam, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h3, hlam, p28297_0]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h23338, h28285, h4, hc12, hc23, hlam, hphi, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h23338, h26245, h28285, h4, hc12, hc23, hlam, hphi, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [h23338, h26247, h28285, h4, hc12, hc23, hlam, hphi, p28297_1]
              · have p28297_0 := h28297c.1
                have p28297_1 := h28297c.2.1
                have p28297_2 := h28297c.2.2.1
                have p28297_3 := h28297c.2.2.2
                linarith only [hlam, p28297_0]
        · linarith only [h23338, h28292, h4, hlam]
      · linarith only [h0, h23337, h23339, h28291, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  rcases m.htr 1 3 4 (by decide) (by decide) with h26251 | h26251
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  rcases m.htr 1 2 5 (by decide) (by decide) with h26249 | h26249
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  rcases m.htr 1 2 4 (by decide) (by decide) with h26247 | h26247
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  rcases m.htr 1 2 3 (by decide) (by decide) with h26245 | h26245
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  rcases m.htr 0 4 5 (by decide) (by decide) with h23339 | h23339
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h19744 h22010 h23337 h23338

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  linarith only [h23337, h23338, h28544, hlam]

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  linarith only [h0, h28546, h4, hlam]

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  linarith only [h0, h19744, h28548, hlam]

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  linarith only [h0, h22010, h28550, hlam]

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h28552 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h28553 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  linarith only [h1, h23338, h28553, hlam]

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h28552 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h28553 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h28555 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  linarith only [h2, h23337, h23338, h28544, h28555, hlam]

end R2N4
