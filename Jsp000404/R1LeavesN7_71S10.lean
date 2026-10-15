import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_71S9

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_M_IR_L_R_L_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h575 | h575
  · rcases m.htr 0 2 4 (by decide) (by decide) with h576 | h576
    · rcases m.htr 0 3 4 (by decide) (by decide) with h577 | h577
      · rcases m.htr 0 3 5 (by decide) (by decide) with h578 | h578
        · rcases m.htr 0 4 5 (by decide) (by decide) with h579 | h579
          · rcases m.htr 1 2 3 (by decide) (by decide) with h580 | h580
            · rcases m.htr 1 3 4 (by decide) (by decide) with h581 | h581
              · rcases m.htr 2 3 4 (by decide) (by decide) with h582 | h582
                · rcases m.htr 2 3 5 (by decide) (by decide) with h583 | h583
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h584 | h584
                    · linarith only [h575, h582, h584, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · rcases h0bigk with h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [hlam, p586_0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h0, h580, hc12, hlam, hphi, ht01, p586_1, u0ehi1]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h0, hlam, p586_0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h0, h580, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p586_1, u4ehi0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h0, h580, hc12, hlam, hphi, ht01, p586_1, u0ehi4]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [hc02, hlam, hphi, p586_1, u0ehi0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [hlam, p586_0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [hc02, hlam, hphi, p586_1, u0ehi2]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h579, h584, hc02, hlam, hphi, ht0b, ht45, ht5b, p586_1, u4ehi3]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h579, h584, hc02, hlam, hphi, ht0b, ht45, ht5b, p586_1, u4ehi3]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [hc03, hlam, hphi, p586_1, u0ehi0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h575, hlam, p586_1]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [hlam, p586_0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h0, h579, h580, h584, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p586_1, u4ehi3]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h0, h579, h580, h584, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p586_1, u4ehi3]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [hc04, hlam, hphi, p586_1, u0ehi0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h576, hlam, p586_0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h577, hlam, p586_0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [hlam, p586_0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h0, h577, h579, h580, h584, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p586_1, u4ehi3]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [hc05, hlam, hphi, p586_1, u0ehi0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h0, h577, h579, h580, hc12, hlam, hphi, ht01, p586_1, u0ehi1]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h578, hlam, p586_0]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [h579, hlam, p586_1]
                      · have p586_0 := h586c.1
                        have p586_1 := h586c.2.1
                        have p586_2 := h586c.2.2.1
                        have p586_3 := h586c.2.2.2
                        linarith only [hlam, p586_0]
                  · linarith only [h0, h578, h580, h582, h583, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h613 | h613
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h614 | h614
                    · linarith only [h0, h577, h580, h582, h613, h614, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h577, h579, h582, h613, h614, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h617 | h617
                    · rcases h0bigk with h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hlam, p618_0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hc01, hlam, hphi, p618_1, u0ehi1]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h0, hlam, p618_0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h577, h617, hc01, hlam, hphi, ht0b, ht45, ht5b, p618_1, u4ehi4]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h0, h578, h580, h613, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p618_1]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hc02, hlam, hphi, p618_1, u0ehi0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hlam, p618_0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h577, h617, hc02, hlam, hphi, ht0b, ht45, ht5b, p618_1, u4ehi4]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h577, h617, hc02, hlam, hphi, ht0b, ht45, ht5b, p618_1, u4ehi4]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hc02, hlam, hphi, p618_1, u0ehi4]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hc03, hlam, hphi, p618_1, u0ehi0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h575, hlam, p618_1]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hlam, p618_0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h0, h577, h580, h617, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p618_1, u4ehi4]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h0, h580, hc12, hlam, hphi, ht01, p618_1, u0ehi4]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hc04, hlam, hphi, p618_1, u0ehi0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h576, hlam, p618_0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h577, hlam, p618_0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hlam, p618_0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h0, h577, h580, hc12, hlam, hphi, ht01, p618_1, u0ehi4]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hc05, hlam, hphi, p618_1, u0ehi0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h0, h577, h579, h580, hc12, hlam, hphi, ht01, p618_1, u0ehi1]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h578, hlam, p618_0]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [h579, hlam, p618_1]
                      · have p618_0 := h618c.1
                        have p618_1 := h618c.2.1
                        have p618_2 := h618c.2.2.1
                        have p618_3 := h618c.2.2.2
                        linarith only [hlam, p618_0]
                    · rcases h0bigk with h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [hlam, p644_0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h575, h577, h579, h582, h617, hc01, hlam, hphi, ht0b, ht45, ht5b, p644_1, u4ehi2]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h0, hlam, p644_0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h0, h579, h580, h582, h617, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p644_1, u4ehi2]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h0, h580, hc12, hlam, hphi, ht01, p644_1, u0ehi4]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [hc02, hlam, hphi, p644_1, u0ehi0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [hlam, p644_0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h577, h579, h582, h617, hc02, hlam, hphi, ht0b, ht45, ht5b, p644_1, u4ehi2]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h579, h582, h617, hc02, hlam, hphi, ht0b, ht45, ht5b, p644_1, u4ehi2]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h579, h582, h617, hc02, hlam, hphi, ht0b, ht45, ht5b, p644_1, u4ehi2]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [hc03, hlam, hphi, p644_1, u0ehi0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h575, hlam, p644_1]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [hlam, p644_0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h0, h579, h580, h582, h617, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p644_1, u4ehi2]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h0, h579, h580, h582, h617, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p644_1, u4ehi2]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [hc04, hlam, hphi, p644_1, u0ehi0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h576, hlam, p644_0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h577, hlam, p644_0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [hlam, p644_0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h0, h577, h579, h580, h582, h617, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p644_1, u4ehi2]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [hc05, hlam, hphi, p644_1, u0ehi0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h0, h577, h579, h580, hc12, hlam, hphi, ht01, p644_1, u0ehi1]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h578, hlam, p644_0]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [h579, hlam, p644_1]
                      · have p644_0 := h644c.1
                        have p644_1 := h644c.2.1
                        have p644_2 := h644c.2.2.1
                        have p644_3 := h644c.2.2.2
                        linarith only [hlam, p644_0]
              · linarith only [h0, h581, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h575, h580, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h672 | h672
            · rcases m.htr 1 3 4 (by decide) (by decide) with h673 | h673
              · rcases m.htr 2 3 4 (by decide) (by decide) with h674 | h674
                · rcases m.htr 2 3 5 (by decide) (by decide) with h675 | h675
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h676 | h676
                    · linarith only [h579, h673, h676, hc14, hlam, hphi, ht01, u0ehi3]
                    · rcases h0bigk with h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [hlam, p678_0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [hc01, hlam, hphi, p678_1, u0ehi1]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h0, hlam, p678_0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p678_1, u4ehi0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h0, h672, hc12, hlam, hphi, ht01, p678_1, u0ehi4]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [hc02, hlam, hphi, p678_1, u0ehi0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [hlam, p678_0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h575, h675, h676, hc02, hlam, hphi, ht0b, ht45, ht5b, p678_1, u4ehi3]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [hc02, hlam, hphi, p678_1, u0ehi3]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h579, hc02, hlam, hphi, p678_1, u0ehi3]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [hc03, hlam, hphi, p678_1, u0ehi0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h575, hlam, p678_1]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [hlam, p678_0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h0, h672, hc12, hlam, hphi, ht01, p678_1, u0ehi3]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h0, h579, h672, hc12, hlam, hphi, ht01, p678_1, u0ehi3]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [hc04, hlam, hphi, p678_1, u0ehi0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h576, hlam, p678_0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h577, hlam, p678_0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [hlam, p678_0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h579, hlam, p678_0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h579, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p678_1, u0ehi0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h579, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p678_1, u0ehi1]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h578, hlam, p678_0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [h579, hc45, hlam, hphi, p678_1, u4ehi0]
                      · have p678_0 := h678c.1
                        have p678_1 := h678c.2.1
                        have p678_2 := h678c.2.2.1
                        have p678_3 := h678c.2.2.2
                        linarith only [hlam, p678_0]
                  · linarith only [h0, h578, h672, h674, h675, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h705 | h705
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h706 | h706
                    · linarith only [h577, h579, h706, hlam]
                    · linarith only [h674, h705, h706, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h709 | h709
                    · linarith only [h577, h579, h709, hlam]
                    · rcases h0bigk with h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hlam, p711_0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hc01, hlam, hphi, p711_1, u0ehi1]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h0, hlam, p711_0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h0, h672, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p711_1, u4ehi0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hc01, hlam, hphi, p711_1, u0ehi4]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hc02, hlam, hphi, p711_1, u0ehi0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hlam, p711_0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hc02, hlam, hphi, p711_1, u0ehi2]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hc02, hlam, hphi, p711_1, u0ehi3]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h579, hc02, hlam, hphi, p711_1, u0ehi3]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hc03, hlam, hphi, p711_1, u0ehi0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h575, hlam, p711_1]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hlam, p711_0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h0, h672, hc12, hlam, hphi, ht01, p711_1, u0ehi3]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h0, h579, h672, hc12, hlam, hphi, ht01, p711_1, u0ehi3]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hc04, hlam, hphi, p711_1, u0ehi0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h576, hlam, p711_0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h577, hlam, p711_0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hlam, p711_0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h579, hlam, p711_0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h579, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p711_1, u0ehi0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h579, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p711_1, u0ehi1]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h578, hlam, p711_0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [h579, hc45, hlam, hphi, p711_1, u4ehi0]
                      · have p711_0 := h711c.1
                        have p711_1 := h711c.2.1
                        have p711_2 := h711c.2.2.1
                        have p711_3 := h711c.2.2.2
                        linarith only [hlam, p711_0]
              · linarith only [h0, h673, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h575, h672, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h739 | h739
          · linarith only [h577, h578, h739, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h741 | h741
            · rcases m.htr 1 3 4 (by decide) (by decide) with h742 | h742
              · rcases m.htr 2 3 4 (by decide) (by decide) with h743 | h743
                · rcases m.htr 2 3 5 (by decide) (by decide) with h744 | h744
                  · linarith only [h575, h578, h744, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h746 | h746
                    · linarith only [h575, h578, h739, h743, h746, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · linarith only [h575, h578, h743, h746, hc45, hlam, hphi, u4ehi3]
                · linarith only [h577, h578, h743, hc23, hc35, hlam, hphi]
              · linarith only [h577, h578, h742, hc13, hc35, hlam, hphi]
            · linarith only [h575, h578, h741, hc35, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h752 | h752
        · rcases m.htr 0 4 5 (by decide) (by decide) with h753 | h753
          · rcases m.htr 1 2 3 (by decide) (by decide) with h754 | h754
            · rcases m.htr 1 3 4 (by decide) (by decide) with h755 | h755
              · linarith only [h577, h755, hc13, hlam, hphi, ht01, u0ehi2]
              · linarith only [h0, h755, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h575, h577, h754, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · linarith only [h577, h752, h753, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h760 | h760
          · rcases m.htr 1 2 3 (by decide) (by decide) with h761 | h761
            · rcases m.htr 1 3 4 (by decide) (by decide) with h762 | h762
              · linarith only [h0, h577, h762, hc13, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h762, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h575, h752, h761, hc35, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h766 | h766
            · rcases m.htr 1 3 4 (by decide) (by decide) with h767 | h767
              · linarith only [h0, h577, h766, h767, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h767, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h575, h577, h760, h766, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h771 | h771
      · linarith only [h575, h576, h771, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h773 | h773
        · rcases m.htr 0 4 5 (by decide) (by decide) with h774 | h774
          · rcases m.htr 1 2 3 (by decide) (by decide) with h775 | h775
            · rcases m.htr 1 3 4 (by decide) (by decide) with h776 | h776
              · linarith only [h771, h775, h776, hc12, hlam, hphi, ht01, u0ehi2]
              · linarith only [h0, h776, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h575, h576, h775, hc24, hlam, hphi, ht12, u1ehi1]
          · linarith only [h575, h576, h773, h774, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
          · rcases m.htr 1 2 3 (by decide) (by decide) with h782 | h782
            · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
              · linarith only [h0, h771, h782, h783, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h783, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h575, h773, h782, hc35, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h787 | h787
            · rcases m.htr 1 3 4 (by decide) (by decide) with h788 | h788
              · linarith only [h0, h771, h787, h788, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h788, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h575, h576, h781, h787, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h792 | h792
    · rcases m.htr 0 3 4 (by decide) (by decide) with h793 | h793
      · rcases m.htr 0 3 5 (by decide) (by decide) with h794 | h794
        · rcases m.htr 0 4 5 (by decide) (by decide) with h795 | h795
          · rcases m.htr 1 2 3 (by decide) (by decide) with h796 | h796
            · linarith only [h575, h792, h795, h796, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h798 | h798
              · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
                · rcases m.htr 2 3 5 (by decide) (by decide) with h800 | h800
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h801 | h801
                    · linarith only [h575, h792, h799, h801, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h575, h792, h795, h801, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h575, h792, h794, h800, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h796, h799, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h0, h793, h798, hc03, hlam, hphi, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h807 | h807
            · linarith only [h575, h807, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h809 | h809
              · rcases m.htr 2 3 4 (by decide) (by decide) with h810 | h810
                · rcases m.htr 2 3 5 (by decide) (by decide) with h811 | h811
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h812 | h812
                    · linarith only [h792, h795, h810, h812, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [hlam, p814_0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h792, hc01, hlam, hphi, ht0b, ht45, ht5b, p814_1, u4ehi2]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h0, hlam, p814_0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h0, h807, hc23, hlam, hphi, ht01, ht12, p814_1, u0ehi3]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h0, h807, hc23, hlam, hphi, ht01, ht12, p814_1, u0ehi4]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [hc02, hlam, hphi, p814_1, u0ehi0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [hlam, p814_0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h575, hlam, p814_0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h575, hc23, hlam, hphi, ht01, ht12, p814_1, u0ehi3]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h575, h795, hc23, hlam, hphi, ht01, ht12, p814_1, u0ehi3]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h0, h807, hc23, hlam, hphi, ht01, ht12, p814_1, u0ehi0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h0, h807, hc23, hlam, hphi, ht01, ht12, p814_1, u0ehi1]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [hlam, p814_0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h0, h807, hc23, hlam, hphi, ht01, ht12, p814_1, u0ehi3]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h0, h795, h807, hc23, hlam, hphi, ht01, ht12, p814_1, u0ehi3]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [hc04, hlam, hphi, p814_1, u0ehi0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h792, hlam, p814_0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h793, hlam, p814_0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [hlam, p814_0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h795, hlam, p814_0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h795, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p814_1, u0ehi0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h792, h795, h810, hc45, hlam, hphi, p814_1, u4ehi3]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h794, hlam, p814_0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [h795, hc45, hlam, hphi, p814_1, u4ehi0]
                      · have p814_0 := h814c.1
                        have p814_1 := h814c.2.1
                        have p814_2 := h814c.2.2.1
                        have p814_3 := h814c.2.2.2
                        linarith only [hlam, p814_0]
                  · linarith only [h807, h811, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h807, h810, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h0, h793, h809, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h843 | h843
          · linarith only [h575, h792, h794, h843, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h845 | h845
            · linarith only [h575, h792, h845, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h847 | h847
              · rcases m.htr 2 3 4 (by decide) (by decide) with h848 | h848
                · rcases m.htr 2 3 5 (by decide) (by decide) with h849 | h849
                  · linarith only [h575, h792, h794, h848, h849, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h845, h849, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h575, h792, h848, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · linarith only [h793, h794, h847, hc13, hc35, hlam, hphi]
      · linarith only [h575, h792, h793, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h855 | h855
      · rcases m.htr 0 3 5 (by decide) (by decide) with h856 | h856
        · rcases m.htr 0 4 5 (by decide) (by decide) with h857 | h857
          · rcases m.htr 1 2 3 (by decide) (by decide) with h858 | h858
            · linarith only [h575, h858, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h860 | h860
              · rcases m.htr 2 3 4 (by decide) (by decide) with h861 | h861
                · rcases m.htr 2 3 5 (by decide) (by decide) with h862 | h862
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h863 | h863
                    · rcases h0bigk with h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c | h864c
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hlam, p864_0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hc01, hlam, hphi, p864_1, u0ehi1]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h0, hlam, p864_0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p864_1, u4ehi0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h0, h858, hc23, hlam, hphi, ht01, ht12, p864_1, u0ehi4]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hc02, hlam, hphi, p864_1, u0ehi0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hlam, p864_0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h575, hlam, p864_0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h792, hlam, p864_1]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hc02, hlam, hphi, p864_1, u0ehi4]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hc03, hlam, hphi, p864_1, u0ehi0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h0, h858, hc23, hlam, hphi, ht01, ht12, p864_1, u0ehi1]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hlam, p864_0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h0, h858, hc23, hlam, hphi, ht01, ht12, p864_1, u0ehi3]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h0, h858, hc23, hlam, hphi, ht01, ht12, p864_1, u0ehi4]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hc04, hlam, hphi, p864_1, u0ehi0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h792, h861, hc23, hlam, hphi, ht01, ht12, p864_1, u0ehi1]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h855, hlam, p864_0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hlam, p864_0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h0, h855, h858, hc23, hlam, hphi, ht01, ht12, p864_1, u0ehi4]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hc05, hlam, hphi, p864_1, u0ehi0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h0, h855, h857, h858, hc23, hlam, hphi, ht01, ht12, p864_1, u0ehi1]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h856, hlam, p864_0]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [h857, hlam, p864_1]
                      · have p864_0 := h864c.1
                        have p864_1 := h864c.2.1
                        have p864_2 := h864c.2.2.1
                        have p864_3 := h864c.2.2.2
                        linarith only [hlam, p864_0]
                    · rcases h0bigk with h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [hlam, p890_0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [hc01, hlam, hphi, p890_1, u0ehi1]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h0, hlam, p890_0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h0, h858, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p890_1, u4ehi0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h0, h857, h858, h863, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p890_1, u4ehi3]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [hc02, hlam, hphi, p890_1, u0ehi0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [hlam, p890_0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h575, hlam, p890_0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h792, hlam, p890_1]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h792, h857, h861, h863, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p890_1, u4ehi3]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h0, h858, hc23, hlam, hphi, ht01, ht12, p890_1, u0ehi0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h0, h858, hc23, hlam, hphi, ht01, ht12, p890_1, u0ehi1]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [hlam, p890_0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h0, h857, h858, h863, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p890_1, u4ehi3]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h0, h857, h858, h863, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p890_1, u4ehi3]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [hc04, hlam, hphi, p890_1, u0ehi0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h792, h861, hc23, hlam, hphi, ht01, ht12, p890_1, u0ehi1]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h855, hlam, p890_0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [hlam, p890_0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h0, h855, h857, h858, h863, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p890_1, u4ehi3]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [hc05, hlam, hphi, p890_1, u0ehi0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h0, h855, h857, h858, hc23, hlam, hphi, ht01, ht12, p890_1, u0ehi1]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h856, hlam, p890_0]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [h857, hlam, p890_1]
                      · have p890_0 := h890c.1
                        have p890_1 := h890c.2.1
                        have p890_2 := h890c.2.2.1
                        have p890_3 := h890c.2.2.2
                        linarith only [hlam, p890_0]
                  · linarith only [h858, h862, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h858, h861, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h0, h855, h860, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h919 | h919
            · linarith only [h575, h919, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h921 | h921
              · rcases m.htr 2 3 4 (by decide) (by decide) with h922 | h922
                · rcases m.htr 2 3 5 (by decide) (by decide) with h923 | h923
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h924 | h924
                    · linarith only [h855, h857, h924, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hc01, hlam, hphi, p926_1, u0ehi1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h0, hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h0, h792, h919, hc23, hlam, hphi, ht01, ht12, p926_1, u0ehi1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h0, h919, hc23, hlam, hphi, ht01, ht12, p926_1, u0ehi4]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h792, hc24, hlam, hphi, ht12, p926_1, u1ehi0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h575, hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h792, hlam, p926_1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h792, h857, hlam, p926_1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h0, h919, hc23, hlam, hphi, ht01, ht12, p926_1, u0ehi0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h0, h919, hc23, hlam, hphi, ht01, ht12, p926_1, u0ehi1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h0, h919, hc23, hlam, hphi, ht01, ht12, p926_1, u0ehi3]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h0, h919, hc23, hlam, hphi, ht01, ht12, p926_1, u0ehi4]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hc04, hlam, hphi, p926_1, u0ehi0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hc04, hlam, hphi, p926_1, u0ehi1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h855, hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h857, hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h0, h856, h919, hc23, hlam, hphi, ht01, ht12, p926_1, u0ehi0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h0, h856, h919, hc23, hlam, hphi, ht01, ht12, p926_1, u0ehi1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h856, hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h0, h856, h919, hc23, hlam, hphi, ht01, ht12, p926_1, u0ehi3]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hlam, p926_0]
                  · linarith only [h0, h856, h919, h923, hlam]
                · linarith only [h919, h922, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h0, h855, h921, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h955 | h955
          · linarith only [h855, h856, h955, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h957 | h957
            · linarith only [h575, h957, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h959 | h959
              · rcases m.htr 2 3 4 (by decide) (by decide) with h960 | h960
                · rcases m.htr 2 3 5 (by decide) (by decide) with h961 | h961
                  · linarith only [h855, h856, h961, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h957, h961, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h0, h855, h957, h960, hc03, hlam, hphi, u0ehi0]
              · linarith only [h855, h856, h959, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h966 | h966
        · rcases m.htr 0 4 5 (by decide) (by decide) with h967 | h967
          · rcases m.htr 1 2 3 (by decide) (by decide) with h968 | h968
            · linarith only [h575, h968, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h970 | h970
              · linarith only [h0, h855, h970, hc13, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h970, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
          · linarith only [h855, h966, h967, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h974 | h974
          · rcases m.htr 1 2 3 (by decide) (by decide) with h975 | h975
            · linarith only [h575, h975, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h977 | h977
              · linarith only [h855, h977, hc13, hlam, hphi, ht01, u0ehi2]
              · linarith only [h0, h977, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h980 | h980
            · linarith only [h575, h980, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h982 | h982
              · linarith only [h0, h855, h982, hc13, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h982, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]

theorem r1l7_20_11_13_14_M_IR_L_R_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_IR_L_R_L_I_L_R_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_IR_L_R_L_I_L_R_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
