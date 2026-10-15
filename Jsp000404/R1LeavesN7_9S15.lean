import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x0_x0_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11549 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11550 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11551 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11552 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 1 2 3 (by decide) (by decide) with h12305 | h12305
  · rcases m.htr 1 2 4 (by decide) (by decide) with h12306 | h12306
    · rcases m.htr 1 3 4 (by decide) (by decide) with h12307 | h12307
      · rcases m.htr 1 3 5 (by decide) (by decide) with h12308 | h12308
        · rcases m.htr 1 4 5 (by decide) (by decide) with h12309 | h12309
          · rcases m.htr 2 3 4 (by decide) (by decide) with h12310 | h12310
            · rcases m.htr 2 3 5 (by decide) (by decide) with h12311 | h12311
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12312 | h12312
                · linarith only [h11549, h11552, h12312, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12314 | h12314
                  · linarith only [h11549, h11552, h12310, h12314, hlam]
                  · rcases h3bigk with h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h7360, hlam, p12316_1]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      rcases p12316_3 (m.d 0 3) (by simp) with h12319 | h12319
                      · rcases p12316_3 (m.d 1 3) (by simp) with h12320 | h12320
                        · rcases p12316_3 (m.d 2 3) (by simp) with h12321 | h12321
                          · linarith only [h11548, h12321, hlam]
                          · rcases p12316_3 (m.d 3 4) (by simp) with h12323 | h12323
                            · linarith only [h11550, h12323, hlam]
                            · rcases p12316_3 (m.d 3 5) (by simp) with h12325 | h12325
                              · linarith only [h11551, h12325, hlam]
                              · rcases h4bigk with h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c | h12327c
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h8811, hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h11552, h12305, h12307, h12309, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h11552, h12305, h12307, h12309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h11552, hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h12305, h12307, h8811, hc01, hc12, hlam, hphi, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  rcases p12327_3 (m.d 0 4) (by simp) with h12335 | h12335
                                  · linarith only [h12335, h8811, hlam]
                                  · linarith only [h11549, h12335, hlam]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  rcases p12327_3 (m.d 0 4) (by simp) with h12338 | h12338
                                  · linarith only [h12338, h8811, hlam]
                                  · linarith only [h11550, h12338, hlam]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h10295, h11552, h12305, h12307, hc01, hc12, hlam, hphi, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h11549, hlam, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h12306, hlam, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h11549, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h12312, hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h11550, hlam, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h12307, hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h12310, hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h12314, hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h12309, hlam, p12327_0]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h12305, h12307, h12309, h12310, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [h12305, h12307, h12309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12327_1]
                                · have p12327_0 := h12327c.1
                                  have p12327_1 := h12327c.2.1
                                  have p12327_2 := h12327c.2.2.1
                                  have p12327_3 := h12327c.2.2.2
                                  linarith only [hlam, p12327_0]
                        · linarith only [h12305, h12320, hlam]
                      · linarith only [h11548, h12319, hlam]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      rcases p12316_3 (m.d 0 3) (by simp) with h12359 | h12359
                      · rcases p12316_3 (m.d 1 3) (by simp) with h12360 | h12360
                        · rcases p12316_3 (m.d 2 3) (by simp) with h12361 | h12361
                          · linarith only [h11548, h12361, hlam]
                          · linarith only [h12310, h12361, hlam]
                        · linarith only [h12307, h12360, hlam]
                      · linarith only [h12359, hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      rcases p12316_3 (m.d 0 3) (by simp) with h12366 | h12366
                      · rcases p12316_3 (m.d 1 3) (by simp) with h12367 | h12367
                        · rcases p12316_3 (m.d 2 3) (by simp) with h12368 | h12368
                          · linarith only [h11548, h12368, hlam]
                          · linarith only [h12311, h12368, hlam]
                        · linarith only [h12308, h12367, hlam]
                      · linarith only [h12366, hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      rcases p12316_3 (m.d 0 3) (by simp) with h12373 | h12373
                      · linarith only [h12373, h7360, hlam]
                      · rcases p12316_3 (m.d 1 3) (by simp) with h12375 | h12375
                        · rcases p12316_3 (m.d 2 3) (by simp) with h12376 | h12376
                          · linarith only [h12305, h12376, hlam]
                          · rcases p12316_3 (m.d 3 4) (by simp) with h12378 | h12378
                            · linarith only [h12307, h12378, hlam]
                            · rcases p12316_3 (m.d 3 5) (by simp) with h12380 | h12380
                              · linarith only [h12308, h12380, hlam]
                              · rcases h4bigk with h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c | h12382c
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h8811, hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h11550, h12305, h12310, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12316_1, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h11550, h12305, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12316_1, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h11552, hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h12305, h12307, h8811, hc01, hc12, hlam, hphi, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  rcases p12382_3 (m.d 0 4) (by simp) with h12390 | h12390
                                  · linarith only [h12390, h8811, hlam]
                                  · linarith only [h11549, h12390, hlam]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  rcases p12382_3 (m.d 0 4) (by simp) with h12393 | h12393
                                  · linarith only [h12393, h8811, hlam]
                                  · linarith only [h11550, h12393, hlam]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h11552, h12305, h12307, h8811, hc01, hc12, hlam, hphi, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h11549, hlam, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h12306, hlam, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h0, h11549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h12312, hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h11550, hlam, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h12307, hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h12310, hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h12314, hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h8811, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h12309, hlam, p12382_0]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h12305, h12307, h12309, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [h12305, h12307, h12309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12382_1]
                                · have p12382_0 := h12382c.1
                                  have p12382_1 := h12382c.2.1
                                  have p12382_2 := h12382c.2.2.1
                                  have p12382_3 := h12382c.2.2.2
                                  linarith only [hlam, p12382_0]
                        · linarith only [h12375, h7360, hlam]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      rcases p12316_3 (m.d 0 3) (by simp) with h12414 | h12414
                      · linarith only [h12414, h7360, hlam]
                      · linarith only [h11548, h12414, hlam]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      rcases p12316_3 (m.d 0 3) (by simp) with h12417 | h12417
                      · linarith only [h12417, h7360, hlam]
                      · linarith only [h11550, h12417, hlam]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      rcases p12316_3 (m.d 0 3) (by simp) with h12420 | h12420
                      · linarith only [h12420, h7360, hlam]
                      · linarith only [h11551, h12420, hlam]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h11548, hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h12305, hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      rcases p12316_3 (m.d 0 3) (by simp) with h12426 | h12426
                      · rcases p12316_3 (m.d 1 3) (by simp) with h12427 | h12427
                        · rcases p12316_3 (m.d 2 3) (by simp) with h12428 | h12428
                          · rcases p12316_3 (m.d 3 4) (by simp) with h12429 | h12429
                            · linarith only [h12429, hlam, p12316_0]
                            · rcases p12316_3 (m.d 3 5) (by simp) with h12431 | h12431
                              · linarith only [h12311, h12431, hlam]
                              · linarith only [h12314, h12431, hlam]
                          · linarith only [h12428, hlam, p12316_0]
                        · linarith only [h12307, h12427, hlam]
                      · linarith only [h11550, h12426, hlam]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      rcases p12316_3 (m.d 0 3) (by simp) with h12437 | h12437
                      · rcases p12316_3 (m.d 1 3) (by simp) with h12438 | h12438
                        · rcases p12316_3 (m.d 2 3) (by simp) with h12439 | h12439
                          · rcases p12316_3 (m.d 3 4) (by simp) with h12440 | h12440
                            · linarith only [h12310, h12440, hlam]
                            · rcases p12316_3 (m.d 3 5) (by simp) with h12442 | h12442
                              · linarith only [h12442, hlam, p12316_0]
                              · rcases h4bigk with h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c | h12444c
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h8811, hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h11552, h12305, h12307, h12309, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h11552, h12305, h12307, h12309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h11552, hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h12305, h12307, h8811, hc01, hc12, hlam, hphi, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  rcases p12444_3 (m.d 0 4) (by simp) with h12452 | h12452
                                  · linarith only [h12452, h8811, hlam]
                                  · linarith only [h11549, h12452, hlam]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  rcases p12444_3 (m.d 0 4) (by simp) with h12455 | h12455
                                  · linarith only [h12455, h8811, hlam]
                                  · linarith only [h11550, h12455, hlam]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h10295, h11552, h12305, h12307, hc01, hc12, hlam, hphi, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h11549, hlam, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h12306, hlam, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h0, h11549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h12312, hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h11550, hlam, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h12307, hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h12310, hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h12314, hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h8811, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h12309, hlam, p12444_0]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h12305, h12307, h12309, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [h12305, h12307, h12309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12444_1]
                                · have p12444_0 := h12444c.1
                                  have p12444_1 := h12444c.2.1
                                  have p12444_2 := h12444c.2.2.1
                                  have p12444_3 := h12444c.2.2.2
                                  linarith only [hlam, p12444_0]
                          · linarith only [h12439, hlam, p12316_0]
                        · linarith only [h12308, h12438, hlam]
                      · linarith only [h11551, h12437, hlam]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h11550, hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h12307, hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h12310, hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h12314, hlam, p12316_1]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h11551, hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h12308, hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h12311, hlam, p12316_0]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [h0, h11548, h12311, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12316_1]
                    · have p12316_0 := h12316c.1
                      have p12316_1 := h12316c.2.1
                      have p12316_2 := h12316c.2.2.1
                      have p12316_3 := h12316c.2.2.2
                      linarith only [hlam, p12316_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12487 | h12487
                · linarith only [h11549, h11552, h12487, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12489 | h12489
                  · linarith only [h11550, h11552, h12489, hlam]
                  · rcases h3bigk with h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c | h12491c
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h7360, hlam, p12491_1]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      rcases p12491_3 (m.d 0 3) (by simp) with h12494 | h12494
                      · rcases p12491_3 (m.d 1 3) (by simp) with h12495 | h12495
                        · rcases p12491_3 (m.d 2 3) (by simp) with h12496 | h12496
                          · linarith only [h11548, h12496, hlam]
                          · rcases p12491_3 (m.d 3 4) (by simp) with h12498 | h12498
                            · linarith only [h11550, h12498, hlam]
                            · rcases p12491_3 (m.d 3 5) (by simp) with h12500 | h12500
                              · linarith only [h11551, h12500, hlam]
                              · linarith only [h12311, h12500, hlam]
                        · linarith only [h12305, h12495, hlam]
                      · linarith only [h11548, h12494, hlam]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h11551, h12310, h12311, hlam, p12491_2]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h11548, h12310, h12311, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p12491_1]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h11551, h12305, h12310, h12311, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12491_1]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      rcases p12491_3 (m.d 0 3) (by simp) with h12509 | h12509
                      · linarith only [h12509, h7360, hlam]
                      · linarith only [h11548, h12509, hlam]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h11551, h12310, h12311, h7360, hlam, p12491_2]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h12310, h12311, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12491_1]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h11548, hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h12305, hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h11551, h12311, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12491_1]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h12311, hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h11550, hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h12307, hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h12310, hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h12489, hlam, p12491_1]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h11551, hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h12308, hlam, p12491_0]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [h11551, h11552, h12305, h12307, h12309, h12310, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12491_1]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      rcases p12491_3 (m.d 0 3) (by simp) with h12527 | h12527
                      · rcases p12491_3 (m.d 1 3) (by simp) with h12528 | h12528
                        · rcases p12491_3 (m.d 2 3) (by simp) with h12529 | h12529
                          · linarith only [h12311, h12529, hlam]
                          · linarith only [h12310, h12529, hlam]
                        · linarith only [h12307, h12528, hlam]
                      · linarith only [h11550, h12527, hlam]
                    · have p12491_0 := h12491c.1
                      have p12491_1 := h12491c.2.1
                      have p12491_2 := h12491c.2.2.1
                      have p12491_3 := h12491c.2.2.2
                      linarith only [hlam, p12491_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h12535 | h12535
              · linarith only [h11550, h11552, h12305, h12307, h12309, h12310, h12535, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12537 | h12537
                · linarith only [h0, h11549, h11550, h11552, h12310, h12537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12539 | h12539
                  · linarith only [h11550, h11552, h12539, hlam]
                  · rcases h3bigk with h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h7360, hlam, p12541_1]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      rcases p12541_3 (m.d 0 3) (by simp) with h12544 | h12544
                      · rcases p12541_3 (m.d 1 3) (by simp) with h12545 | h12545
                        · rcases p12541_3 (m.d 2 3) (by simp) with h12546 | h12546
                          · linarith only [h11548, h12546, hlam]
                          · rcases p12541_3 (m.d 3 4) (by simp) with h12548 | h12548
                            · linarith only [h11550, h12548, hlam]
                            · linarith only [h12310, h12548, hlam]
                        · linarith only [h12305, h12545, hlam]
                      · linarith only [h11548, h12544, hlam]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      rcases p12541_3 (m.d 0 3) (by simp) with h12553 | h12553
                      · rcases p12541_3 (m.d 1 3) (by simp) with h12554 | h12554
                        · rcases p12541_3 (m.d 2 3) (by simp) with h12555 | h12555
                          · linarith only [h11548, h12555, hlam]
                          · rcases p12541_3 (m.d 3 4) (by simp) with h12557 | h12557
                            · linarith only [h12557, hlam, p12541_0]
                            · rcases p12541_3 (m.d 3 5) (by simp) with h12559 | h12559
                              · linarith only [h11551, h12559, hlam]
                              · linarith only [h12539, h12559, hlam]
                        · linarith only [h12307, h12554, hlam]
                      · linarith only [h12553, hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      rcases p12541_3 (m.d 0 3) (by simp) with h12564 | h12564
                      · rcases p12541_3 (m.d 1 3) (by simp) with h12565 | h12565
                        · rcases p12541_3 (m.d 2 3) (by simp) with h12566 | h12566
                          · linarith only [h11548, h12566, hlam]
                          · rcases p12541_3 (m.d 3 4) (by simp) with h12568 | h12568
                            · linarith only [h11550, h12568, hlam]
                            · rcases p12541_3 (m.d 3 5) (by simp) with h12570 | h12570
                              · linarith only [h12570, hlam, p12541_0]
                              · rcases h4bigk with h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c | h12572c
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [hlam, p12572_0]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h8811, hlam, p12572_0]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h11552, h12305, h12307, h12309, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h11552, h12305, h12307, h12309, h12310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h11552, hlam, p12572_0]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h12305, h12307, h8811, hc01, hc12, hlam, hphi, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [hlam, p12572_0]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  rcases p12572_3 (m.d 0 4) (by simp) with h12580 | h12580
                                  · linarith only [h12580, h8811, hlam]
                                  · linarith only [h11549, h12580, hlam]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h12305, h12307, h12310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h10295, h11552, h12305, h12307, hc01, hc12, hlam, hphi, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h11549, hlam, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h12306, hlam, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [hlam, p12572_0]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h12310, hlam, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h12537, hlam, p12572_0]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h11550, hlam, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h12307, hlam, p12572_0]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h11548, h12310, h12539, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12541_1, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [hlam, p12572_0]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h12539, hlam, p12572_0]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h12309, hlam, p12572_0]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h12305, h12307, h12309, h12310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [h12305, h12307, h12309, h12310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12572_1]
                                · have p12572_0 := h12572c.1
                                  have p12572_1 := h12572c.2.1
                                  have p12572_2 := h12572c.2.2.1
                                  have p12572_3 := h12572c.2.2.2
                                  linarith only [hlam, p12572_0]
                        · linarith only [h12308, h12565, hlam]
                      · linarith only [h12564, hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h11550, h12305, h12310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12541_1]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h11550, h11552, h12307, h12309, h12310, hlam, p12541_2]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      rcases p12541_3 (m.d 0 3) (by simp) with h12605 | h12605
                      · linarith only [h12605, h7360, hlam]
                      · linarith only [h11550, h12605, hlam]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      rcases p12541_3 (m.d 0 3) (by simp) with h12608 | h12608
                      · linarith only [h12608, h7360, hlam]
                      · linarith only [h11551, h12608, hlam]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h11548, hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h12305, hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h12310, hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h12535, hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h11550, hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h12307, hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h11550, h11552, h12307, h12309, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12541_1]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h12539, hlam, p12541_1]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h11551, hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h12308, hlam, p12541_0]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      rcases p12541_3 (m.d 0 3) (by simp) with h12623 | h12623
                      · rcases p12541_3 (m.d 1 3) (by simp) with h12624 | h12624
                        · rcases p12541_3 (m.d 2 3) (by simp) with h12625 | h12625
                          · linarith only [h12625, hlam, p12541_0]
                          · rcases p12541_3 (m.d 3 4) (by simp) with h12627 | h12627
                            · linarith only [h12539, h12627, hlam]
                            · linarith only [h12310, h12627, hlam]
                        · linarith only [h12305, h12624, hlam]
                      · linarith only [h11548, h12623, hlam]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [h11551, h12310, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12541_1]
                    · have p12541_0 := h12541c.1
                      have p12541_1 := h12541c.2.1
                      have p12541_2 := h12541c.2.2.1
                      have p12541_3 := h12541c.2.2.2
                      linarith only [hlam, p12541_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h12634 | h12634
            · rcases m.htr 2 3 5 (by decide) (by decide) with h12635 | h12635
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12636 | h12636
                · linarith only [h12309, h12636, h8811, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12638 | h12638
                  · linarith only [h12309, h12638, h8811, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases h3bigk with h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c | h12640c
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h7360, hlam, p12640_1]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      rcases p12640_3 (m.d 0 3) (by simp) with h12643 | h12643
                      · rcases p12640_3 (m.d 1 3) (by simp) with h12644 | h12644
                        · rcases p12640_3 (m.d 2 3) (by simp) with h12645 | h12645
                          · linarith only [h11548, h12645, hlam]
                          · rcases p12640_3 (m.d 3 4) (by simp) with h12647 | h12647
                            · linarith only [h11550, h12647, hlam]
                            · rcases p12640_3 (m.d 3 5) (by simp) with h12649 | h12649
                              · linarith only [h11551, h12649, hlam]
                              · rcases h4bigk with h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c | h12651c
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h8811, hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12309, h8811, hc24, hc45, hlam, hphi, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12309, h8811, hc34, hc45, hlam, hphi, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h11552, hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12309, hc04, hc45, hlam, hphi, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12309, hc24, hc45, hlam, hphi, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12309, hc34, hc45, hlam, hphi, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12309, hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h11549, hlam, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12306, hlam, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h0, h11549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12636, hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h11550, hlam, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12307, hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12634, hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h12638, hlam, p12651_0]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [h8811, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [hc24, hc45, hlam, hphi, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p12651_1]
                                · have p12651_0 := h12651c.1
                                  have p12651_1 := h12651c.2.1
                                  have p12651_2 := h12651c.2.2.1
                                  have p12651_3 := h12651c.2.2.2
                                  linarith only [hlam, p12651_0]
                        · linarith only [h12305, h12644, hlam]
                      · linarith only [h11548, h12643, hlam]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      rcases p12640_3 (m.d 0 3) (by simp) with h12679 | h12679
                      · rcases p12640_3 (m.d 1 3) (by simp) with h12680 | h12680
                        · rcases p12640_3 (m.d 2 3) (by simp) with h12681 | h12681
                          · linarith only [h11548, h12681, hlam]
                          · linarith only [h12634, h12681, hlam]
                        · linarith only [h12307, h12680, hlam]
                      · linarith only [h12679, hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      rcases p12640_3 (m.d 0 3) (by simp) with h12686 | h12686
                      · rcases p12640_3 (m.d 1 3) (by simp) with h12687 | h12687
                        · rcases p12640_3 (m.d 2 3) (by simp) with h12688 | h12688
                          · linarith only [h11548, h12688, hlam]
                          · linarith only [h12635, h12688, hlam]
                        · linarith only [h12308, h12687, hlam]
                      · linarith only [h12686, hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      rcases p12640_3 (m.d 0 3) (by simp) with h12693 | h12693
                      · linarith only [h12693, h7360, hlam]
                      · rcases p12640_3 (m.d 1 3) (by simp) with h12695 | h12695
                        · rcases p12640_3 (m.d 2 3) (by simp) with h12696 | h12696
                          · linarith only [h12305, h12696, hlam]
                          · rcases p12640_3 (m.d 3 4) (by simp) with h12698 | h12698
                            · linarith only [h12307, h12698, hlam]
                            · rcases p12640_3 (m.d 3 5) (by simp) with h12700 | h12700
                              · linarith only [h12308, h12700, hlam]
                              · rcases h4bigk with h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c | h12702c
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h8811, hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h11550, h12305, h12634, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12640_1, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h11550, h12305, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12640_1, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h11552, hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h8811, hc01, hc14, hlam, hphi, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h12309, h12634, hc34, hc45, hlam, hphi, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h12309, hc34, hc45, hlam, hphi, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h12309, hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h11549, hlam, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h12306, hlam, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h0, h11549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h12636, hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h11550, hlam, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h12307, hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h12634, hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h12638, hlam, p12702_0]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [h8811, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [hc24, hc45, hlam, hphi, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p12702_1]
                                · have p12702_0 := h12702c.1
                                  have p12702_1 := h12702c.2.1
                                  have p12702_2 := h12702c.2.2.1
                                  have p12702_3 := h12702c.2.2.2
                                  linarith only [hlam, p12702_0]
                        · linarith only [h12695, h7360, hlam]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      rcases p12640_3 (m.d 0 3) (by simp) with h12730 | h12730
                      · linarith only [h12730, h7360, hlam]
                      · linarith only [h11548, h12730, hlam]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      rcases p12640_3 (m.d 0 3) (by simp) with h12733 | h12733
                      · linarith only [h12733, h7360, hlam]
                      · linarith only [h11550, h12733, hlam]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      rcases p12640_3 (m.d 0 3) (by simp) with h12736 | h12736
                      · linarith only [h12736, h7360, hlam]
                      · linarith only [h11551, h12736, hlam]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h11548, hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h12305, hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      rcases p12640_3 (m.d 0 3) (by simp) with h12742 | h12742
                      · rcases p12640_3 (m.d 1 3) (by simp) with h12743 | h12743
                        · rcases p12640_3 (m.d 2 3) (by simp) with h12744 | h12744
                          · rcases p12640_3 (m.d 3 4) (by simp) with h12745 | h12745
                            · linarith only [h12745, hlam, p12640_0]
                            · rcases p12640_3 (m.d 3 5) (by simp) with h12747 | h12747
                              · linarith only [h12635, h12747, hlam]
                              · linarith only [h12638, h12747, hlam]
                          · linarith only [h12744, hlam, p12640_0]
                        · linarith only [h12307, h12743, hlam]
                      · linarith only [h11550, h12742, hlam]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      rcases p12640_3 (m.d 0 3) (by simp) with h12753 | h12753
                      · rcases p12640_3 (m.d 1 3) (by simp) with h12754 | h12754
                        · rcases p12640_3 (m.d 2 3) (by simp) with h12755 | h12755
                          · rcases p12640_3 (m.d 3 4) (by simp) with h12756 | h12756
                            · linarith only [h12634, h12756, hlam]
                            · rcases p12640_3 (m.d 3 5) (by simp) with h12758 | h12758
                              · linarith only [h12758, hlam, p12640_0]
                              · rcases h4bigk with h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c | h12760c
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h8811, hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h11552, h12634, hc34, hc45, hlam, hphi, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h11552, hc34, hc45, hlam, hphi, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h11552, hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h12309, h8811, hc01, hc15, hlam, hphi, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h12309, h12634, hc34, hc45, hlam, hphi, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h12309, hc34, hc45, hlam, hphi, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h12309, hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h11549, hlam, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h12306, hlam, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h0, h11549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h12636, hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h11550, hlam, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h12307, hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h12634, hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h12638, hlam, p12760_0]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [h12634, hc34, hc45, hlam, hphi, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p12760_1]
                                · have p12760_0 := h12760c.1
                                  have p12760_1 := h12760c.2.1
                                  have p12760_2 := h12760c.2.2.1
                                  have p12760_3 := h12760c.2.2.2
                                  linarith only [hlam, p12760_0]
                          · linarith only [h12755, hlam, p12640_0]
                        · linarith only [h12308, h12754, hlam]
                      · linarith only [h11551, h12753, hlam]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h11550, hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h12307, hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h12634, hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h12638, hlam, p12640_1]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h11551, hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h12308, hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h12635, hlam, p12640_0]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [h0, h11548, h12635, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12640_1]
                    · have p12640_0 := h12640c.1
                      have p12640_1 := h12640c.2.1
                      have p12640_2 := h12640c.2.2.1
                      have p12640_3 := h12640c.2.2.2
                      linarith only [hlam, p12640_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12799 | h12799
                · linarith only [h0, h10295, h11549, h12309, h12799, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12801 | h12801
                  · linarith only [h12309, h12801, h8811, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases h3bigk with h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c | h12803c
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h7360, hlam, p12803_1]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      rcases p12803_3 (m.d 0 3) (by simp) with h12806 | h12806
                      · rcases p12803_3 (m.d 1 3) (by simp) with h12807 | h12807
                        · rcases p12803_3 (m.d 2 3) (by simp) with h12808 | h12808
                          · linarith only [h11548, h12808, hlam]
                          · rcases p12803_3 (m.d 3 4) (by simp) with h12810 | h12810
                            · linarith only [h11550, h12810, hlam]
                            · rcases p12803_3 (m.d 3 5) (by simp) with h12812 | h12812
                              · linarith only [h11551, h12812, hlam]
                              · linarith only [h12635, h12812, hlam]
                        · linarith only [h12305, h12807, hlam]
                      · linarith only [h11548, h12806, hlam]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h11551, h12634, h12635, hlam, p12803_2]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h12305, h12634, h12635, h7360, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12803_1]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h11551, h12305, h12634, h12635, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12803_1]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      rcases p12803_3 (m.d 0 3) (by simp) with h12821 | h12821
                      · linarith only [h12821, h7360, hlam]
                      · linarith only [h11548, h12821, hlam]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h11551, h12634, h12635, h7360, hlam, p12803_2]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h12634, h12635, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12803_1]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h11548, hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h12305, hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h11551, h12635, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12803_1]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h12635, hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h11550, hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h12307, hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h12634, hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h12801, hlam, p12803_1]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h11551, hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h12308, hlam, p12803_0]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [h0, h11548, h11551, h12634, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12803_1]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      rcases p12803_3 (m.d 0 3) (by simp) with h12839 | h12839
                      · rcases p12803_3 (m.d 1 3) (by simp) with h12840 | h12840
                        · rcases p12803_3 (m.d 2 3) (by simp) with h12841 | h12841
                          · linarith only [h12635, h12841, hlam]
                          · linarith only [h12634, h12841, hlam]
                        · linarith only [h12307, h12840, hlam]
                      · linarith only [h11550, h12839, hlam]
                    · have p12803_0 := h12803c.1
                      have p12803_1 := h12803c.2.1
                      have p12803_2 := h12803c.2.2.1
                      have p12803_3 := h12803c.2.2.2
                      linarith only [hlam, p12803_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h12847 | h12847
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12848 | h12848
                · linarith only [h11550, h12309, h12634, h12847, h12848, h8811, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h12634, h12847, h12848, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12851 | h12851
                · linarith only [h12309, h12851, h8811, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12853 | h12853
                  · linarith only [h12309, h12853, h8811, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases h3bigk with h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c | h12855c
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h7360, hlam, p12855_1]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      rcases p12855_3 (m.d 0 3) (by simp) with h12858 | h12858
                      · rcases p12855_3 (m.d 1 3) (by simp) with h12859 | h12859
                        · rcases p12855_3 (m.d 2 3) (by simp) with h12860 | h12860
                          · linarith only [h11548, h12860, hlam]
                          · rcases p12855_3 (m.d 3 4) (by simp) with h12862 | h12862
                            · linarith only [h11550, h12862, hlam]
                            · linarith only [h12634, h12862, hlam]
                        · linarith only [h12305, h12859, hlam]
                      · linarith only [h11548, h12858, hlam]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      rcases p12855_3 (m.d 0 3) (by simp) with h12867 | h12867
                      · rcases p12855_3 (m.d 1 3) (by simp) with h12868 | h12868
                        · rcases p12855_3 (m.d 2 3) (by simp) with h12869 | h12869
                          · linarith only [h11548, h12869, hlam]
                          · rcases p12855_3 (m.d 3 4) (by simp) with h12871 | h12871
                            · linarith only [h12871, hlam, p12855_0]
                            · rcases p12855_3 (m.d 3 5) (by simp) with h12873 | h12873
                              · linarith only [h11551, h12873, hlam]
                              · linarith only [h12853, h12873, hlam]
                        · linarith only [h12307, h12868, hlam]
                      · linarith only [h12867, hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      rcases p12855_3 (m.d 0 3) (by simp) with h12878 | h12878
                      · rcases p12855_3 (m.d 1 3) (by simp) with h12879 | h12879
                        · rcases p12855_3 (m.d 2 3) (by simp) with h12880 | h12880
                          · linarith only [h11548, h12880, hlam]
                          · rcases p12855_3 (m.d 3 4) (by simp) with h12882 | h12882
                            · linarith only [h11550, h12882, hlam]
                            · rcases p12855_3 (m.d 3 5) (by simp) with h12884 | h12884
                              · linarith only [h12884, hlam, p12855_0]
                              · rcases h4bigk with h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c | h12886c
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [hlam, p12886_0]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h8811, hlam, p12886_0]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12309, h8811, hc24, hc45, hlam, hphi, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12309, h12634, h8811, hc23, hc45, hlam, hphi, ht34, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h11552, hlam, p12886_0]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12309, hc04, hc45, hlam, hphi, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [hlam, p12886_0]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12309, hc24, hc45, hlam, hphi, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12309, h12634, hc23, hc45, hlam, hphi, ht34, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12309, hlam, p12886_0]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h11549, hlam, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12306, hlam, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [hlam, p12886_0]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12634, hlam, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12851, hlam, p12886_0]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h11550, hlam, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12307, hlam, p12886_0]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h11550, h12309, h8811, hc24, hc45, hlam, hphi, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [hlam, p12886_0]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12853, hlam, p12886_0]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12634, hc23, hc45, hlam, hphi, ht34, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [h12634, hc23, hc45, hlam, hphi, ht34, p12886_1]
                                · have p12886_0 := h12886c.1
                                  have p12886_1 := h12886c.2.1
                                  have p12886_2 := h12886c.2.2.1
                                  have p12886_3 := h12886c.2.2.2
                                  linarith only [hlam, p12886_0]
                        · linarith only [h12308, h12879, hlam]
                      · linarith only [h12878, hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h11550, h12305, h12634, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12855_1]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      rcases p12855_3 (m.d 0 3) (by simp) with h12916 | h12916
                      · linarith only [h12916, h7360, hlam]
                      · linarith only [h11548, h12916, hlam]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      rcases p12855_3 (m.d 0 3) (by simp) with h12919 | h12919
                      · linarith only [h12919, h7360, hlam]
                      · linarith only [h11550, h12919, hlam]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      rcases p12855_3 (m.d 0 3) (by simp) with h12922 | h12922
                      · linarith only [h12922, h7360, hlam]
                      · linarith only [h11551, h12922, hlam]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h11548, hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h12305, hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h12634, hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h12847, hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h11550, hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h12307, hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h11550, h11552, hc23, hc45, hlam, hphi, ht34, p12855_1]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h12853, hlam, p12855_1]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h11551, hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h12308, hlam, p12855_0]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      rcases p12855_3 (m.d 0 3) (by simp) with h12937 | h12937
                      · rcases p12855_3 (m.d 1 3) (by simp) with h12938 | h12938
                        · rcases p12855_3 (m.d 2 3) (by simp) with h12939 | h12939
                          · linarith only [h12939, hlam, p12855_0]
                          · rcases p12855_3 (m.d 3 4) (by simp) with h12941 | h12941
                            · linarith only [h12853, h12941, hlam]
                            · linarith only [h12634, h12941, hlam]
                        · linarith only [h12305, h12938, hlam]
                      · linarith only [h11548, h12937, hlam]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [h11551, h12634, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12855_1]
                    · have p12855_0 := h12855c.1
                      have p12855_1 := h12855c.2.1
                      have p12855_2 := h12855c.2.2.1
                      have p12855_3 := h12855c.2.2.2
                      linarith only [hlam, p12855_0]
        · linarith only [h11551, h12308, h7360, hlam]
      · linarith only [h11550, h12307, h7360, hlam]
    · linarith only [h0, h11549, h12306, hlam]
  · linarith only [h0, h11548, h12305, hlam]

set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x0_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11549 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11550 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11551 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 4 5 (by decide) (by decide) with h11552 | h11552
  · exact r1l7_13_24_L_I_H_I_s11_x0_x0_x0_x0_x0 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h11549 h11550 h11551 h11552
  · exact r1l7_13_24_L_I_H_I_s11_x0_x0_x0_x0_x1 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h11549 h11550 h11551 h11552

end R2N4
