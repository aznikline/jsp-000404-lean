import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_67S1

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_R_L_I_L_R_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h413 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h569 | h569
  · rcases m.htr 0 2 4 (by decide) (by decide) with h570 | h570
    · rcases m.htr 0 2 5 (by decide) (by decide) with h571 | h571
      · rcases m.htr 0 3 4 (by decide) (by decide) with h572 | h572
        · rcases m.htr 0 3 5 (by decide) (by decide) with h573 | h573
          · rcases m.htr 0 4 5 (by decide) (by decide) with h574 | h574
            · rcases m.htr 1 2 3 (by decide) (by decide) with h575 | h575
              · rcases m.htr 1 2 4 (by decide) (by decide) with h576 | h576
                · rcases m.htr 1 2 5 (by decide) (by decide) with h577 | h577
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h578 | h578
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h579 | h579
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h580 | h580
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h581 | h581
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h582 | h582
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h583 | h583
                              · linarith only [h569, h580, h583, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases h0bigk with h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h413, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h413, h575, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p585_1, u5ehi0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h569, h580, h582, h583, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h570, h582, h583, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p585_1, u5ehi0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h413, h575, hc01, hc12, hlam, hphi, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h569, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h413, h570, h575, h582, h583, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h413, h571, h575, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p585_1, u2ehi4]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h570, hc01, hc12, hlam, hphi, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h570, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h572, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h413, h571, h572, h575, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p585_1, u2ehi4]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h571, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h573, hlam, p585_0]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [h574, hlam, p585_1]
                                · have p585_0 := h585c.1
                                  have p585_1 := h585c.2.1
                                  have p585_2 := h585c.2.2.1
                                  have p585_3 := h585c.2.2.2
                                  linarith only [hlam, p585_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h611 | h611
                              · linarith only [h0, h569, h580, h611, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases h0bigk with h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [hlam, p613_0]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h0, hlam, p613_1]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h413, hlam, p613_0]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h574, hc01, hlam, hphi, ht0b, ht5b, p613_1, u5ehi0]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h413, h574, h575, h582, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p613_1, u2ehi3]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p613_1]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [hlam, p613_0]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h0, h413, hc01, hc12, hlam, hphi, p613_1]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h0, h574, h582, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p613_1, u2ehi3]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h0, h574, h582, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p613_1, u2ehi3]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h413, h575, hc01, hc12, hlam, hphi, p613_1]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h569, hlam, p613_1]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [hlam, p613_0]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h413, h574, h575, h582, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p613_1, u2ehi3]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h413, h574, h575, h582, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p613_1, u2ehi3]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h0, h570, hc01, hc12, hlam, hphi, p613_1]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h570, hlam, p613_0]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h572, hlam, p613_0]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [hlam, p613_0]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h413, h572, h574, h575, h582, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p613_1, u2ehi3]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p613_1]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h571, hlam, p613_1]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h573, hlam, p613_0]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [h574, hlam, p613_1]
                                · have p613_0 := h613c.1
                                  have p613_1 := h613c.2.1
                                  have p613_2 := h613c.2.2.1
                                  have p613_3 := h613c.2.2.2
                                  linarith only [hlam, p613_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h639 | h639
                            · linarith only [h413, h573, h575, h580, h581, h639, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h641 | h641
                              · linarith only [h413, h573, h575, h580, h581, h639, h641, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases h0bigk with h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c | h643c
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [hlam, p643_0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h0, hlam, p643_1]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h413, hlam, p643_0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h574, hc01, hlam, hphi, ht0b, ht5b, p643_1, u5ehi0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p643_1, u5ehi0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p643_1]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [hlam, p643_0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h0, h572, h574, h580, h581, h641, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p643_1, u2ehi3]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h0, h574, h580, h581, h641, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p643_1, u2ehi3]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p643_1, u5ehi0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h413, hc01, hc13, hlam, hphi, p643_1]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h569, hlam, p643_1]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [hlam, p643_0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h0, h569, h574, h580, h581, h641, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p643_1, u2ehi3]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h0, h569, h571, h580, h581, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p643_1, u2ehi3]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h0, h570, hc01, hc12, hlam, hphi, p643_1]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h570, hlam, p643_0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h572, hlam, p643_0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [hlam, p643_0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h0, h569, h572, h574, h580, h581, h641, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p643_1, u2ehi3]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p643_1]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h571, hlam, p643_1]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h573, hlam, p643_0]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [h574, hlam, p643_1]
                                · have p643_0 := h643c.1
                                  have p643_1 := h643c.2.1
                                  have p643_2 := h643c.2.2.1
                                  have p643_3 := h643c.2.2.2
                                  linarith only [hlam, p643_0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h669 | h669
                          · linarith only [h0, h569, h572, h580, h669, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h671 | h671
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h672 | h672
                              · rcases h0bigk with h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [hlam, p673_0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h0, hlam, p673_1]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h413, hlam, p673_0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h574, hc01, hlam, hphi, ht0b, ht5b, p673_1, u5ehi0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h413, h575, hc12, hlam, hphi, ht01, ht0b, ht5b, p673_1, u5ehi0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p673_1]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [hlam, p673_0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h0, h572, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p673_1]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h0, h570, h671, hc12, hlam, hphi, ht01, ht0b, ht5b, p673_1, u5ehi4]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p673_1, u5ehi0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h413, h575, hc01, hc12, hlam, hphi, p673_1]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h569, hlam, p673_1]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [hlam, p673_0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h413, h570, h575, h671, hc12, hlam, hphi, ht01, ht0b, ht5b, p673_1, u5ehi4]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h413, h571, h575, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p673_1, u2ehi4]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h0, h570, hc01, hc12, hlam, hphi, p673_1]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h570, hlam, p673_0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h572, hlam, p673_0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [hlam, p673_0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h573, h669, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p673_1, u2ehi2]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p673_1]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h571, hlam, p673_1]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h573, hlam, p673_0]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [h574, hlam, p673_1]
                                · have p673_0 := h673c.1
                                  have p673_1 := h673c.2.1
                                  have p673_2 := h673c.2.2.1
                                  have p673_3 := h673c.2.2.2
                                  linarith only [hlam, p673_0]
                              · linarith only [h576, h580, h671, h672, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h700 | h700
                              · linarith only [h413, h572, h575, h580, h671, h700, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h413, h572, h574, h575, h580, h700, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h413, h573, h579, hlam]
                    · linarith only [h413, h572, h578, hlam]
                  · linarith only [h0, h569, h577, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h570, h576, hlam]
              · linarith only [h0, h569, h575, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h708 | h708
              · rcases m.htr 1 2 4 (by decide) (by decide) with h709 | h709
                · rcases m.htr 1 2 5 (by decide) (by decide) with h710 | h710
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h711 | h711
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h712 | h712
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h713 | h713
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h714 | h714
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h715 | h715
                            · linarith only [h570, h574, h715, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h717 | h717
                              · linarith only [h569, h570, h574, h713, h717, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases h0bigk with h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h0, hlam, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h413, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h570, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi3]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h570, h574, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi3]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h0, h569, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi2]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h0, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi3]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h0, h570, h574, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi3]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h413, hc01, hc13, hlam, hphi, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h569, hlam, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h0, h569, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi3]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h0, h569, h570, h574, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi3]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h574, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h570, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h572, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h574, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h571, hlam, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h573, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h570, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi3]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hlam, p719_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h745 | h745
                            · linarith only [h570, h574, h745, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h747 | h747
                              · linarith only [h573, h574, h713, h714, h747, hlam]
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
                                  linarith only [h0, hlam, p749_1]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h413, hlam, p749_0]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h570, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p749_1, u2ehi3]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h413, h573, h708, h713, h714, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p749_1, u2ehi3]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p749_1]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [hlam, p749_0]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h0, h413, hc01, hc12, hlam, hphi, p749_1]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h0, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p749_1, u2ehi3]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h0, h573, h713, h714, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p749_1, u2ehi3]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h413, h708, hc01, hc12, hlam, hphi, p749_1]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h569, hlam, p749_1]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [hlam, p749_0]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h413, h570, h708, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p749_1, u2ehi3]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h413, h573, h708, h713, h714, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p749_1, u2ehi3]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h0, h570, hc01, hc12, hlam, hphi, p749_1]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h570, hlam, p749_0]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h572, hlam, p749_0]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [hlam, p749_0]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h574, hlam, p749_0]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p749_1]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h571, hlam, p749_1]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h573, hlam, p749_0]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [h574, hc04, hc45, hlam, hphi, p749_1]
                                · have p749_0 := h749c.1
                                  have p749_1 := h749c.2.1
                                  have p749_2 := h749c.2.2.1
                                  have p749_3 := h749c.2.2.2
                                  linarith only [hlam, p749_0]
                        · linarith only [h572, h574, h713, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h413, h573, h712, hlam]
                    · linarith only [h413, h572, h711, hlam]
                  · linarith only [h0, h569, h710, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h569, h709, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h569, h708, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
            · linarith only [h572, h573, h781, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
              · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
                · rcases m.htr 1 2 5 (by decide) (by decide) with h785 | h785
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h786 | h786
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h787 | h787
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h788 | h788
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h789 | h789
                          · linarith only [h569, h573, h789, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h791 | h791
                            · linarith only [h570, h572, h573, h783, h787, h791, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h793 | h793
                              · linarith only [h569, h570, h573, h781, h783, h787, h788, h793, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases h0bigk with h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [hlam, p795_0]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h0, hlam, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h413, hlam, p795_0]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h570, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p795_1, u2ehi3]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h413, h573, hlam, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [hlam, p795_0]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h0, h569, h788, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h0, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p795_1, u2ehi3]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p795_1, u5ehi0]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h413, h783, hc01, hc12, hlam, hphi, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h569, hlam, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [hlam, p795_0]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h413, h570, h783, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p795_1, u2ehi3]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h573, hlam, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h0, h570, hc01, hc12, hlam, hphi, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h570, hlam, p795_0]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h572, hlam, p795_0]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [hlam, p795_0]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h781, hlam, p795_0]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h571, hlam, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h569, h788, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p795_1, u2ehi3]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [h573, h783, h787, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p795_1]
                                · have p795_0 := h795c.1
                                  have p795_1 := h795c.2.1
                                  have p795_2 := h795c.2.2.1
                                  have p795_3 := h795c.2.2.2
                                  linarith only [hlam, p795_0]
                        · linarith only [h572, h573, h783, h787, h788, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h822 | h822
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h823 | h823
                          · linarith only [h413, h787, h823, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h825 | h825
                            · linarith only [h570, h781, h825, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h827 | h827
                              · linarith only [h413, h569, h781, h787, h822, h827, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · rcases h0bigk with h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [hlam, p829_0]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h0, hlam, p829_1]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h413, hlam, p829_0]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h570, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p829_1, u2ehi3]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h413, h787, h827, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p829_1, u5ehi0]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p829_1]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [hlam, p829_0]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h0, h569, h822, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p829_1]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h0, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p829_1, u2ehi3]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p829_1, u5ehi0]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h413, hc01, hc13, hlam, hphi, p829_1]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h569, hlam, p829_1]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [hlam, p829_0]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h413, h570, h787, h827, hc45, hlam, hphi, ht23, ht34, p829_1, u2ehi3]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h573, hlam, p829_1]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h0, h570, hc01, hc12, hlam, hphi, p829_1]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h570, hlam, p829_0]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h572, hlam, p829_0]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [hlam, p829_0]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h781, hlam, p829_0]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p829_1]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h571, hlam, p829_1]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h569, h822, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p829_1, u2ehi3]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [h573, h827, hc04, hc45, hlam, hphi, p829_1]
                                · have p829_0 := h829c.1
                                  have p829_1 := h829c.2.1
                                  have p829_2 := h829c.2.2.1
                                  have p829_3 := h829c.2.2.2
                                  linarith only [hlam, p829_0]
                        · linarith only [h413, h572, h787, h822, hc23, hc35, hlam, hphi]
                    · linarith only [h413, h572, h786, hlam]
                  · linarith only [h0, h569, h785, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h569, h784, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h571, h783, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h860 | h860
          · rcases m.htr 0 4 5 (by decide) (by decide) with h861 | h861
            · rcases m.htr 1 2 3 (by decide) (by decide) with h862 | h862
              · rcases m.htr 1 2 4 (by decide) (by decide) with h863 | h863
                · rcases m.htr 1 2 5 (by decide) (by decide) with h864 | h864
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h865 | h865
                    · linarith only [h572, h860, h862, h865, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h867 | h867
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h868 | h868
                        · linarith only [h569, h865, h867, h868, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h870 | h870
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h871 | h871
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h872 | h872
                              · rcases h0bigk with h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [hlam, p873_0]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h0, hlam, p873_1]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h413, hlam, p873_0]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h569, h572, h870, h872, hc01, hlam, hphi, ht0b, ht5b, p873_1, u5ehi4]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h413, h865, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p873_1, u5ehi0]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p873_1]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [hlam, p873_0]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h0, h569, h870, hc12, hlam, hphi, ht01, ht0b, ht5b, p873_1, u5ehi3]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h0, h569, h572, h870, h872, hc12, hlam, hphi, ht01, ht0b, ht5b, p873_1, u5ehi4]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p873_1, u5ehi0]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h413, h865, hc01, hc34, hlam, hphi, ht12, ht23, p873_1]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h569, hlam, p873_1]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [hlam, p873_0]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h572, hlam, p873_1]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h413, h571, h865, hc34, hlam, hphi, ht23, p873_1, u2ehi4]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h0, h570, hc01, hc12, hlam, hphi, p873_1]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h570, hlam, p873_0]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h569, h870, h872, hc04, hlam, hphi, ht0b, ht5b, p873_1, u5ehi4]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [hlam, p873_0]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h571, h572, hc34, hlam, hphi, ht23, p873_1, u2ehi4]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p873_1]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h571, hlam, p873_1]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h860, hlam, p873_0]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [h861, hlam, p873_1]
                                · have p873_0 := h873c.1
                                  have p873_1 := h873c.2.1
                                  have p873_2 := h873c.2.2.1
                                  have p873_3 := h873c.2.2.2
                                  linarith only [hlam, p873_0]
                              · linarith only [h413, h569, h865, h870, h872, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                            · linarith only [h413, h860, h861, h865, h871, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h413, h860, h865, h870, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h413, h860, h867, hlam]
                  · linarith only [h0, h569, h864, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h570, h863, hlam]
              · linarith only [h0, h569, h862, hlam]
            · linarith only [h572, h860, h861, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h907 | h907
            · rcases m.htr 1 2 3 (by decide) (by decide) with h908 | h908
              · rcases m.htr 1 2 4 (by decide) (by decide) with h909 | h909
                · rcases m.htr 1 2 5 (by decide) (by decide) with h910 | h910
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h911 | h911
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h912 | h912
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h913 | h913
                        · linarith only [h569, h572, h913, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h915 | h915
                          · linarith only [h569, h860, h915, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h917 | h917
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h918 | h918
                              · rcases h0bigk with h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [hlam, p919_0]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h0, hlam, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h413, hlam, p919_0]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h570, h917, hc01, hlam, hphi, ht0b, ht5b, p919_1, u5ehi4]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h413, h860, h908, h911, h918, hc12, hlam, hphi, ht01, ht0b, ht5b, p919_1, u5ehi0]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [hlam, p919_0]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h0, h569, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p919_1, u2ehi2]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h0, h570, h917, hc12, hlam, hphi, ht01, ht0b, ht5b, p919_1, u5ehi4]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h0, h571, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p919_1, u2ehi4]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h413, h908, hc01, hc12, hlam, hphi, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h569, hlam, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [hlam, p919_0]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h572, hlam, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h860, hlam, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h0, h570, hc01, hc12, hlam, hphi, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h570, hlam, p919_0]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h572, h908, h911, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [hlam, p919_0]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h571, h572, h908, h911, h915, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p919_1, u2ehi2]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h571, hlam, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h569, h860, h908, h911, h918, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p919_1, u2ehi2]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [h907, hlam, p919_1]
                                · have p919_0 := h919c.1
                                  have p919_1 := h919c.2.1
                                  have p919_2 := h919c.2.2.1
                                  have p919_3 := h919c.2.2.2
                                  linarith only [hlam, p919_0]
                              · linarith only [h570, h572, h917, h918, hlam]
                            · linarith only [h572, h907, h913, h917, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h572, h907, h911, h912, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h948 | h948
                      · linarith only [h569, h860, h911, h948, hc34, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h950 | h950
                        · linarith only [h413, h911, h950, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h952 | h952
                          · linarith only [h413, h569, h948, h952, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h954 | h954
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h955 | h955
                              · rcases h0bigk with h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, hlam, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h413, hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h570, h954, hc01, hlam, hphi, ht0b, ht5b, p956_1, u5ehi4]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h413, h860, h948, h955, hc03, hc34, hlam, hphi, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, h569, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p956_1, u2ehi2]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, h907, hc12, hlam, hphi, ht01, ht0b, ht5b, p956_1, u5ehi0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p956_1, u5ehi0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h413, h948, h955, hc01, hc34, hlam, hphi, ht12, ht23, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h569, hlam, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h572, hlam, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h860, hlam, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, h570, hc01, hc12, hlam, hphi, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h570, hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h572, hc03, hc34, hlam, hphi, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h571, h572, h952, hc34, hlam, hphi, ht23, p956_1, u2ehi2]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, h571, hc01, hc12, hlam, hphi, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h571, hlam, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h569, h860, h955, hc34, hlam, hphi, ht23, p956_1, u2ehi2]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h907, hlam, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [hlam, p956_0]
                              · linarith only [h570, h572, h954, h955, hlam]
                            · linarith only [h572, h907, h954, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h569, h910, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h569, h909, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h569, h908, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h987 | h987
              · rcases m.htr 1 2 4 (by decide) (by decide) with h988 | h988
                · rcases m.htr 1 2 5 (by decide) (by decide) with h989 | h989
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h990 | h990
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h991 | h991
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h992 | h992
                        · linarith only [h569, h572, h992, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h994 | h994
                          · linarith only [h569, h860, h994, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h996 | h996
                            · linarith only [h570, h907, h996, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h998 | h998
                              · linarith only [h569, h572, h907, h987, h990, h998, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h569, h572, h998, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h569, h572, h990, h991, hc35, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1002 | h1002
                      · linarith only [h1002, h569, h860, h990, hc34, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1004 | h1004
                        · linarith only [h1004, h413, h990, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1006 | h1006
                          · linarith only [h1002, h1006, h413, h569, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1008 | h1008
                            · linarith only [h1008, h570, h907, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1010 | h1010
                              · linarith only [h1010, h569, h572, h907, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h1010, h569, h572, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h569, h989, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h571, h988, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h571, h987, hc23, hlam, hphi, u2ehi4]
      · linarith only [h569, h571, hc25, hlam, hphi, u2ehi2]
    · linarith only [h569, h570, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1018 | h1018
    · linarith only [h1018, h569, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1020 | h1020
      · linarith only [h1020, h569, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1022 | h1022
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1023 | h1023
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1024 | h1024
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1025 | h1025
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1026 | h1026
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1027 | h1027
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1028 | h1028
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1029 | h1029
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1030 | h1030
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1031 | h1031
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1032 | h1032
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1033 | h1033
                              · linarith only [h1022, h1025, h1033, h569, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases h0bigk with h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [hlam, p1035_0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h0, hlam, p1035_1]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h413, hlam, p1035_0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1024, hc01, hlam, hphi, ht0b, ht5b, p1035_1, u5ehi0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h0, h1020, h1025, h1030, h1032, hc12, hlam, hphi, ht01, ht0b, ht5b, p1035_1, u5ehi0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1020, h1025, h1030, h1032, hc01, hc12, hlam, hphi, p1035_1]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [hlam, p1035_0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h569, hlam, p1035_0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1018, hlam, p1035_1]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1020, hlam, p1035_0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h413, hc01, hc13, hlam, hphi, p1035_1]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1025, h569, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1035_1, u2ehi0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [hlam, p1035_0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1024, h1025, h1033, h569, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1035_1]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1020, h1025, h569, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1035_1, u2ehi0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1018, h1025, h1030, hc01, hc12, hlam, hphi, p1035_1]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1018, h1025, h1030, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1035_1, u2ehi0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1022, hlam, p1035_0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [hlam, p1035_0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1018, h1020, h1025, h1030, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1035_1, u2ehi0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1020, h1025, h1030, h1032, hc01, hc12, hlam, hphi, p1035_1]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1035_1, u2ehi0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1023, hlam, p1035_0]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [h1024, hlam, p1035_1]
                                · have p1035_0 := h1035c.1
                                  have p1035_1 := h1035c.2.1
                                  have p1035_2 := h1035c.2.2.1
                                  have p1035_3 := h1035c.2.2.2
                                  linarith only [hlam, p1035_0]
                            · linarith only [h1018, h1032, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1031, h569, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1030, h569, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1023, h1029, h413, hlam]
                    · linarith only [h1022, h1025, h1028, h569, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h1025, h1027, hc25, hlam, hphi, u2ehi2]
                · linarith only [h1025, h1026, h569, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1068 | h1068
                · linarith only [h1025, h1068, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1070 | h1070
                  · linarith only [h1025, h1070, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1072 | h1072
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1073 | h1073
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1074 | h1074
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1075 | h1075
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1076 | h1076
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1077 | h1077
                              · rcases h0bigk with h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h0, hlam, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h413, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1022, h1077, hc01, hlam, hphi, ht0b, ht5b, p1078_1, u5ehi4]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h0, h1070, h1074, h1076, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1078_1, u5ehi0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h0, h1070, h1074, h1076, hc01, hc23, hlam, hphi, ht12, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h569, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1018, hlam, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1020, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h413, hc01, hc13, hlam, hphi, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h569, hc23, hlam, hphi, p1078_1, u2ehi0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1022, h1077, h569, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1078_1, u5ehi4]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1020, h569, hc23, hlam, hphi, p1078_1, u2ehi0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1018, h1074, hc01, hc23, hlam, hphi, ht12, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1018, h1074, hc23, hlam, hphi, p1078_1, u2ehi0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1022, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1020, h1022, h1025, h413, hc23, hlam, hphi, p1078_1, u2ehi0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1020, h1074, h1076, hc01, hc23, hlam, hphi, ht12, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1078_1, u2ehi0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1023, hlam, p1078_0]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [h1024, hlam, p1078_1]
                                · have p1078_0 := h1078c.1
                                  have p1078_1 := h1078c.2.1
                                  have p1078_2 := h1078c.2.2.1
                                  have p1078_3 := h1078c.2.2.2
                                  linarith only [hlam, p1078_0]
                              · rcases h0bigk with h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [hlam, p1104_0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h0, hlam, p1104_1]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h413, hlam, p1104_0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1024, hc01, hlam, hphi, ht0b, ht5b, p1104_1, u5ehi0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h0, h1020, h1070, h1074, h1076, hc23, hlam, hphi, p1104_1, u2ehi0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h0, h1070, h1074, h1076, hc01, hc23, hlam, hphi, ht12, p1104_1]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [hlam, p1104_0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h569, hlam, p1104_0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1018, hlam, p1104_1]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1020, hlam, p1104_0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1025, h413, hc01, hc23, hlam, hphi, ht12, p1104_1]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1025, h413, hc23, hlam, hphi, p1104_1, u2ehi0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [hlam, p1104_0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1024, h1025, h1077, h413, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1104_1]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1020, h1025, h413, hc23, hlam, hphi, p1104_1, u2ehi0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1018, h1074, hc01, hc23, hlam, hphi, ht12, p1104_1]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1018, h1074, hc23, hlam, hphi, p1104_1, u2ehi0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1022, hlam, p1104_0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [hlam, p1104_0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1020, h1022, h1025, h413, hc23, hlam, hphi, p1104_1, u2ehi0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1020, h1074, h1076, hc01, hc23, hlam, hphi, ht12, p1104_1]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1104_1, u2ehi0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1023, hlam, p1104_0]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [h1024, hlam, p1104_1]
                                · have p1104_0 := h1104c.1
                                  have p1104_1 := h1104c.2.1
                                  have p1104_2 := h1104c.2.2.1
                                  have p1104_3 := h1104c.2.2.2
                                  linarith only [hlam, p1104_0]
                            · linarith only [h1018, h1076, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1075, h569, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1074, h569, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1023, h1073, h413, hlam]
                    · linarith only [h1022, h1072, h413, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1135 | h1135
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1136 | h1136
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1137 | h1137
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1138 | h1138
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1139 | h1139
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1140 | h1140
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1141 | h1141
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1142 | h1142
                            · linarith only [h1018, h1024, h1135, h1140, h1142, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · linarith only [h1018, h1142, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1023, h1141, h569, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1140, h569, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1023, h1139, h413, h569, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h1022, h1135, h1138, h569, hlam]
                  · linarith only [h1135, h1137, h569, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1135, h1136, h569, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1151 | h1151
                · linarith only [h1135, h1151, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1153 | h1153
                  · linarith only [h1135, h1153, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1155 | h1155
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1156 | h1156
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1157 | h1157
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1158 | h1158
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1159 | h1159
                            · linarith only [h1018, h1024, h1157, h1159, hc23, hlam, hphi, u2ehi0]
                            · linarith only [h0, h1151, h1159, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h1023, h1135, h1158, h413, hlam]
                        · linarith only [h1157, h569, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1023, h1156, h413, hlam]
                    · linarith only [h1022, h1155, h413, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1166 | h1166
            · linarith only [h1022, h1023, h1166, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1168 | h1168
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1169 | h1169
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1170 | h1170
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1171 | h1171
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1172 | h1172
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1173 | h1173
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1174 | h1174
                          · linarith only [h1018, h1022, h1023, h1168, h1174, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1174, h569, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1022, h1173, h569, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1168, h1172, h569, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1022, h1023, h1168, h1171, h569, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1168, h1170, h569, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1168, h1169, h569, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1182 | h1182
                · linarith only [h1168, h1182, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1184 | h1184
                  · linarith only [h1168, h1184, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1186 | h1186
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1187 | h1187
                      · linarith only [h1023, h1168, h1187, h569, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1189 | h1189
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1190 | h1190
                          · linarith only [h1018, h1022, h1187, h1190, h413, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1190, h569, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h1022, h1168, h1189, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h1022, h1186, h413, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1195 | h1195
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1196 | h1196
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1197 | h1197
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1198 | h1198
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1199 | h1199
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1200 | h1200
                    · linarith only [h1022, h1195, h1200, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h1197, h1200, h569, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1197, h1199, h569, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1197, h1198, h569, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1205 | h1205
                · linarith only [h1197, h1205, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1207 | h1207
                  · linarith only [h1197, h1207, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1209 | h1209
                    · linarith only [h1022, h1195, h1209, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1211 | h1211
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1212 | h1212
                        · linarith only [h1207, h1209, h1211, h1212, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1212, h569, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1195, h1211, h413, hlam]
            · linarith only [h1022, h1195, h1196, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1217 | h1217
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1218 | h1218
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1219 | h1219
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1220 | h1220
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1221 | h1221
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1222 | h1222
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1223 | h1223
                        · linarith only [h1022, h1223, h569, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1218, h1221, h1223, h569, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1022, h1221, h1222, hc03, hc35, hlam, hphi]
                    · linarith only [h1218, h1221, h569, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1018, h1219, h1220, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1218, h1219, h569, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1230 | h1230
                · linarith only [h1218, h1230, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1232 | h1232
                  · linarith only [h1218, h1232, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1234 | h1234
                    · linarith only [h1022, h1218, h1234, h569, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1236 | h1236
                      · linarith only [h1195, h1234, h1236, h569, hc34, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1238 | h1238
                        · linarith only [h1218, h1234, h1238, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1238, h569, hc34, hlam, hphi, ht23, u2ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1241 | h1241
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1242 | h1242
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1243 | h1243
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1244 | h1244
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1245 | h1245
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1246 | h1246
                        · linarith only [h1022, h1246, h569, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1241, h1244, h1246, h569, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1022, h1244, h1245, hc03, hc35, hlam, hphi]
                    · linarith only [h1241, h1244, h569, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1018, h1242, h1243, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1241, h1242, h569, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1253 | h1253
                · linarith only [h1241, h1253, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1255 | h1255
                  · linarith only [h1241, h1255, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1257 | h1257
                    · linarith only [h1022, h1241, h1257, h569, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1259 | h1259
                      · linarith only [h1195, h1257, h1259, h569, hc34, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1261 | h1261
                        · linarith only [h1241, h1257, h1261, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1261, h569, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_20_12_13_15_H_I_L_R_L_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h413 | h413
  · exact r1l7_20_12_13_15_H_I_L_R_L_I_L_R_x1_x0 m hb0 hb2 hb3 hb5 h0 h413
  · exact r1l7_20_12_13_15_H_I_L_R_L_I_L_R_x1_x1 m hb0 hb2 hb3 hb5 h0 h413

theorem r1l7_20_12_13_15_H_I_L_R_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_I_L_R_L_I_L_R_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_I_L_R_L_I_L_R_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
