import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_74S6

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_23_L_0_H_I_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h496 | h496
  · rcases m.htr 0 2 3 (by decide) (by decide) with h497 | h497
    · rcases m.htr 0 3 4 (by decide) (by decide) with h498 | h498
      · rcases m.htr 0 3 5 (by decide) (by decide) with h499 | h499
        · rcases m.htr 1 2 3 (by decide) (by decide) with h500 | h500
          · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
            · linarith only [h0, h496, h501, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · linarith only [h0, h496, h498, h500, h501, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
          · linarith only [h0, h500, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h505 | h505
          · rcases m.htr 1 3 4 (by decide) (by decide) with h506 | h506
            · linarith only [h0, h496, h506, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · linarith only [h498, h499, h506, hc13, hc35, hlam, hphi]
          · linarith only [h0, h505, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h510 | h510
        · rcases m.htr 1 2 3 (by decide) (by decide) with h511 | h511
          · rcases m.htr 1 3 4 (by decide) (by decide) with h512 | h512
            · linarith only [h0, h496, h498, h512, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h514 | h514
              · linarith only [h0, h496, h514, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h498, h510, h511, h514, hc23, hc34, hlam, hphi]
          · linarith only [h0, h511, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h518 | h518
          · rcases m.htr 1 3 4 (by decide) (by decide) with h519 | h519
            · linarith only [h0, h496, h498, h519, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h521 | h521
              · linarith only [h0, h496, h510, h521, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
                · linarith only [h496, h498, h518, h523, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h525 | h525
                  · linarith only [h496, h510, h518, h525, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h527 | h527
                    · rcases h3bigk with h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h510, h518, h527, hc23, hc34, hlam, hphi, p528_1]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h0, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p528_1, u2elo1]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h498, hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h510, hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h496, hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h0, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p528_1, u2elo1]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h519, hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h521, hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h497, hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h518, hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h523, hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h525, hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [hc03, hc34, hlam, hphi, p528_1]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h518, hc23, hc34, hlam, hphi, p528_1]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p528_1]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h496, h510, h518, hc23, hc34, hlam, hphi, p528_1]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h496, h518, hc23, hc35, hlam, hphi, p528_1]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h518, hc23, hc35, hlam, hphi, p528_1]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [hc23, hc35, hlam, hphi, p528_1]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [h527, hlam, p528_0]
                      · have p528_0 := h528c.1
                        have p528_1 := h528c.2.1
                        have p528_2 := h528c.2.2.1
                        have p528_3 := h528c.2.2.2
                        linarith only [hlam, p528_0]
                    · rcases h3bigk with h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h0, h496, h518, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p554_1, u2elo1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h0, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p554_1, u2elo1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h498, hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h510, hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h496, hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h0, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p554_1, u2elo1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h519, hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h521, hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h497, hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h518, hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h523, hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h525, hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h527, hc03, hc45, hlam, hphi, ht34, p554_1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h518, h527, hc23, hc45, hlam, hphi, ht34, p554_1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h527, hc23, hc45, hlam, hphi, ht34, p554_1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [hlam, p554_0]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h527, hlam, p554_1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h496, h518, h527, hc23, hc45, hlam, hphi, ht34, p554_1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h518, h527, hc23, hc45, hlam, hphi, ht34, p554_1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h527, hc23, hc45, hlam, hphi, ht34, p554_1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [h519, h527, hc14, hc45, hlam, hphi, p554_1]
                      · have p554_0 := h554c.1
                        have p554_1 := h554c.2.1
                        have p554_2 := h554c.2.2.1
                        have p554_3 := h554c.2.2.2
                        linarith only [hlam, p554_0]
          · linarith only [h0, h518, hc01, hlam, hphi, ht12, u2elo2]
    · linarith only [h0, h496, h497, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h582 | h582
    · rcases m.htr 0 3 4 (by decide) (by decide) with h583 | h583
      · rcases m.htr 0 3 5 (by decide) (by decide) with h584 | h584
        · rcases m.htr 1 2 3 (by decide) (by decide) with h585 | h585
          · rcases m.htr 1 3 4 (by decide) (by decide) with h586 | h586
            · rcases m.htr 1 3 5 (by decide) (by decide) with h587 | h587
              · rcases m.htr 2 3 4 (by decide) (by decide) with h588 | h588
                · rcases m.htr 2 3 5 (by decide) (by decide) with h589 | h589
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h590 | h590
                    · linarith only [h582, h588, h590, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases h3bigk with h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h496, hlam, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h0, h582, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p592_1, u2elo1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h0, h582, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p592_1, u2elo1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h0, h582, h590, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p592_1, u2elo1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h585, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p592_1, u2elo1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h585, h589, h590, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p592_1, u2elo1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h585, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p592_1, u2elo1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h585, h590, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p592_1, u2elo1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h582, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h585, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p592_1, u2elo2]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h0, h582, h590, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p592_1, u2elo1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h583, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h586, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h588, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h590, hlam, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h584, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h587, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h589, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h496, h584, h585, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p592_1, u2elo1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hlam, p592_0]
                  · linarith only [h496, h584, h585, h588, h589, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h619 | h619
                  · linarith only [h496, h583, h585, h588, h619, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h621 | h621
                    · rcases h3bigk with h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c | h622c
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h496, hlam, p622_1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h496, h585, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p622_1, u2elo1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h496, h585, h619, h621, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p622_1, u2elo1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h496, h585, h619, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p622_1, u2elo1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h585, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p622_1, u2elo1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h585, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p622_1, u2elo1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h585, h621, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p622_1, u2elo1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h585, h619, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p622_1, u2elo1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h582, hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h585, hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h588, hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h619, hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h583, hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h586, hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h583, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p622_1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h496, h583, h585, h619, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p622_1, u2elo1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h584, hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h587, hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [hc23, hc35, hlam, hphi, p622_1]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [h621, hlam, p622_0]
                      · have p622_0 := h622c.1
                        have p622_1 := h622c.2.1
                        have p622_2 := h622c.2.2.1
                        have p622_3 := h622c.2.2.2
                        linarith only [hlam, p622_0]
                    · rcases h3bigk with h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h496, hlam, p648_1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h496, h585, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p648_1, u2elo1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h496, h585, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p648_1, u2elo1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h496, h585, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p648_1, u2elo1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h585, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p648_1, u2elo1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h585, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p648_1, u2elo1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h585, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p648_1, u2elo1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h585, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p648_1, u2elo1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h582, hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h585, hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h588, hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h619, hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h583, hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h586, hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h583, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p648_1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h621, hlam, p648_1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h584, hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h587, hlam, p648_0]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [hc23, hc35, hlam, hphi, p648_1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [h496, h584, h585, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p648_1, u2elo1]
                      · have p648_0 := h648c.1
                        have p648_1 := h648c.2.1
                        have p648_2 := h648c.2.2.1
                        have p648_3 := h648c.2.2.2
                        linarith only [hlam, p648_0]
              · linarith only [h496, h584, h587, hlam]
            · linarith only [h496, h583, h586, hlam]
          · linarith only [h0, h585, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h677 | h677
          · rcases m.htr 1 3 4 (by decide) (by decide) with h678 | h678
            · rcases m.htr 1 3 5 (by decide) (by decide) with h679 | h679
              · linarith only [h583, h584, h677, h679, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h681 | h681
                · rcases m.htr 2 3 5 (by decide) (by decide) with h682 | h682
                  · linarith only [h582, h679, h682, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h684 | h684
                    · linarith only [h0, h582, h681, h684, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases h3bigk with h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h496, hlam, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h584, h681, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h496, h679, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h584, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h679, hc03, hc35, hlam, hphi, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h679, h681, h684, hc34, hc45, hlam, hphi, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h679, h684, hc34, hc45, hlam, hphi, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h679, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h582, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h677, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p686_1, u2elo2]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h682, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h583, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h678, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h681, hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h684, hlam, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h684, hc03, hc45, hlam, hphi, ht34, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h684, hc13, hc45, hlam, hphi, ht34, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h681, h684, hc34, hc45, hlam, hphi, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [h684, hc34, hc45, hlam, hphi, p686_1]
                      · have p686_0 := h686c.1
                        have p686_1 := h686c.2.1
                        have p686_2 := h686c.2.2.1
                        have p686_3 := h686c.2.2.2
                        linarith only [hlam, p686_0]
                · linarith only [h583, h584, h681, hc23, hc35, hlam, hphi]
            · linarith only [h496, h583, h678, hlam]
          · linarith only [h0, h677, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h715 | h715
        · rcases m.htr 1 2 3 (by decide) (by decide) with h716 | h716
          · rcases m.htr 1 3 4 (by decide) (by decide) with h717 | h717
            · linarith only [h583, h715, h716, h717, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h719 | h719
              · rcases m.htr 2 3 4 (by decide) (by decide) with h720 | h720
                · linarith only [h496, h717, h720, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h722 | h722
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h723 | h723
                    · rcases h3bigk with h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h496, hlam, p724_1]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h722, h723, hc03, hc45, hlam, hphi, ht0b, ht5b, p724_1]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h583, hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h496, h717, h723, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p724_1]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h717, hc03, hc34, hlam, hphi, p724_1]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h717, h722, h723, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p724_1]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h717, hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h717, h723, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p724_1]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h582, hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h716, hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h720, hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h723, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p724_1, u2elo2]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [hc03, hc34, hlam, hphi, p724_1]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [hc13, hc34, hlam, hphi, p724_1]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p724_1]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        rcases p724_3 (m.d 0 3) (by simp) with h744 | h744
                        · linarith only [h583, h744, hlam]
                        · linarith only [h715, h744, hlam]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h715, hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h719, hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h722, hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [h723, hlam, p724_0]
                      · have p724_0 := h724c.1
                        have p724_1 := h724c.2.1
                        have p724_2 := h724c.2.2.1
                        have p724_3 := h724c.2.2.2
                        linarith only [hlam, p724_0]
                    · linarith only [h496, h717, h723, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h496, h715, h717, h722, hc23, hc34, hlam, hphi]
              · linarith only [h496, h715, h719, hlam]
          · linarith only [h0, h716, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h756 | h756
          · rcases m.htr 1 3 4 (by decide) (by decide) with h757 | h757
            · linarith only [h496, h583, h756, h757, hc01, hlam, hphi, ht12, u2elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h759 | h759
              · linarith only [h496, h715, h756, h759, hc01, hlam, hphi, ht12, u2elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h761 | h761
                · linarith only [h496, h757, h761, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h763 | h763
                  · linarith only [h496, h759, h763, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h765 | h765
                    · rcases h3bigk with h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h496, hlam, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h496, h759, h765, hc23, hc34, hlam, hphi, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h583, hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h715, hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h759, h765, hc03, hc34, hlam, hphi, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h759, h765, hc23, hc34, hlam, hphi, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h757, hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h759, hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h582, hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h756, hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h761, hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h763, hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h496, hc01, hc34, hlam, hphi, ht12, ht23, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [hc13, hc34, hlam, hphi, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h496, h715, hc01, hc34, hlam, hphi, ht12, ht23, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h496, hc01, hc35, hlam, hphi, ht12, ht23, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h496, hc01, hc35, hlam, hphi, ht12, ht23, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [hc23, hc35, hlam, hphi, p766_1]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [h765, hlam, p766_0]
                      · have p766_0 := h766c.1
                        have p766_1 := h766c.2.1
                        have p766_2 := h766c.2.2.1
                        have p766_3 := h766c.2.2.2
                        linarith only [hlam, p766_0]
                    · linarith only [h496, h757, h765, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h756, hc01, hlam, hphi, ht12, u2elo2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h794 | h794
      · rcases m.htr 0 3 5 (by decide) (by decide) with h795 | h795
        · rcases m.htr 1 2 3 (by decide) (by decide) with h796 | h796
          · linarith only [h582, h796, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h796, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h799 | h799
          · linarith only [h0, h582, h799, hc01, hlam, hphi, ht12, u2elo1]
          · linarith only [h0, h799, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h802 | h802
        · rcases m.htr 1 2 3 (by decide) (by decide) with h803 | h803
          · linarith only [h0, h582, h803, hc01, hlam, hphi, ht12, u2elo1]
          · linarith only [h0, h803, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h806 | h806
          · linarith only [h0, h582, h806, hc01, hlam, hphi, ht12, u2elo1]
          · linarith only [h0, h806, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_12_23_L_0_H_I (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_23_L_0_H_I_x0 m hb2 hb3 h0
  · exact r1l7_12_23_L_0_H_I_x1 m hb2 hb3 h0

end R2N4
