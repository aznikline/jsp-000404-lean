import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S8
import Jsp000404.R1LeavesN7_7S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7968000 in
set_option maxHeartbeats 7968000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5543 | h5543
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5544 | h5544
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5545 | h5545
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5546 | h5546
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5547 | h5547
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5548 | h5548
            · linarith only [h4, h5544, h5548, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5550 | h5550
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5551 | h5551
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5552 | h5552
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5553 | h5553
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5554 | h5554
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5555 | h5555
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5556 | h5556
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5557 | h5557
                            · linarith only [h0, h4, h5550, h5557, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5559 | h5559
                              · linarith only [h5555, h5557, h5559, hlam]
                              · rcases h1bigk with h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c | h5561c
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h5550, h5554, h5555, h5557, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5561_1]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h5548, h5550, h5554, h5555, h5557, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5561_1]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h5554, h5555, h5557, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5561_1]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  rcases p5561_3 (m.d 0 1) (by simp) with h5566 | h5566
                                  · rcases p5561_3 (m.d 1 2) (by simp) with h5567 | h5567
                                    · linarith only [h0, h5567, hlam]
                                    · linarith only [h5551, h5567, hlam]
                                  · linarith only [h5566, hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h0, hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h5548, hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h0, h4, h5554, h5555, h5557, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5561_1]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5561_1, u5ehi1]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h1, hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h1, h5550, h5555, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5561_1]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h1, h5554, h5555, h5557, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5561_1]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p5561_1, u5ehi1]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h2, hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h5550, hlam, p5561_1]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h5552, hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h0, h5550, h5551, h5556, hc01, hlam, hphi, ht0b, ht5b, p5561_1, u5ehi3]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h3, hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h5551, hlam, p5561_1]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h5553, hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [h5554, hlam, p5561_0]
                                · have p5561_0 := h5561c.1
                                  have p5561_1 := h5561c.2.1
                                  have p5561_2 := h5561c.2.2.1
                                  have p5561_3 := h5561c.2.2.2
                                  linarith only [hlam, p5561_0]
                          · linarith only [h4, h5544, h5556, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h4, h5544, h5555, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5593 | h5593
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5594 | h5594
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5595 | h5595
                            · linarith only [h5550, h5554, h5595, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5597 | h5597
                              · linarith only [h5550, h5554, h5593, h5597, hlam]
                              · rcases h1bigk with h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h5551, h5594, hc01, hlam, hphi, ht0b, ht5b, p5599_1, u5ehi3]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h5548, h5551, h5594, hc01, hlam, hphi, ht0b, ht5b, p5599_1, u5ehi3]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  rcases p5599_3 (m.d 0 1) (by simp) with h5603 | h5603
                                  · rcases p5599_3 (m.d 1 2) (by simp) with h5604 | h5604
                                    · linarith only [h0, h5604, hlam]
                                    · linarith only [h5550, h5604, hlam]
                                  · linarith only [h5603, hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  rcases p5599_3 (m.d 0 1) (by simp) with h5608 | h5608
                                  · rcases p5599_3 (m.d 1 2) (by simp) with h5609 | h5609
                                    · linarith only [h0, h5609, hlam]
                                    · linarith only [h5551, h5609, hlam]
                                  · linarith only [h5608, hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h0, hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h5548, hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  rcases p5599_3 (m.d 0 1) (by simp) with h5616 | h5616
                                  · rcases p5599_3 (m.d 1 2) (by simp) with h5617 | h5617
                                    · rcases p5599_3 (m.d 1 3) (by simp) with h5618 | h5618
                                      · rcases p5599_3 (m.d 1 4) (by simp) with h5619 | h5619
                                        · linarith only [h5550, h5619, hlam]
                                        · rcases p5599_3 (m.d 1 5) (by simp) with h5621 | h5621
                                          · linarith only [h5551, h5621, hlam]
                                          · linarith only [h5554, h5621, hlam]
                                      · linarith only [h5552, h5618, hlam]
                                    · linarith only [h5550, h5617, hlam]
                                  · linarith only [h2, h5616, hlam]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h1, h5548, h5551, h5594, hc01, hlam, hphi, ht0b, ht5b, p5599_1, u5ehi3]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h1, hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h1, h5550, h5593, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5599_1]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  rcases p5599_3 (m.d 0 1) (by simp) with h5631 | h5631
                                  · rcases p5599_3 (m.d 1 2) (by simp) with h5632 | h5632
                                    · linarith only [h5548, h5632, hlam]
                                    · linarith only [h5550, h5632, hlam]
                                  · linarith only [h2, h5631, hlam]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h1, h5551, h5594, hc01, hlam, hphi, ht0b, ht5b, p5599_1, u5ehi3]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h2, hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h5550, hlam, p5599_1]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h5552, hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h5554, hlam, p5599_1]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h3, hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h5551, hlam, p5599_1]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h5553, hlam, p5599_0]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [h4, h5543, h5547, h5550, h5554, h5593, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5599_1]
                                · have p5599_0 := h5599c.1
                                  have p5599_1 := h5599c.2.1
                                  have p5599_2 := h5599c.2.2.1
                                  have p5599_3 := h5599c.2.2.2
                                  linarith only [hlam, p5599_0]
                          · linarith only [h4, h5543, h5547, h5554, h5594, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h4, h5543, h5547, h5551, h5554, h5593, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h4, h5543, h5546, h5547, h5548, h5551, h5553, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h4, h5545, h5548, h5551, h5552, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h4, h5544, h5551, hc12, hc23, hlam, hphi]
              · linarith only [h4, h5543, h5550, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5653 | h5653
            · linarith only [h4, h5544, h5653, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5655 | h5655
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5656 | h5656
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5657 | h5657
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5658 | h5658
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5659 | h5659
                      · linarith only [h2, h5547, h5659, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5661 | h5661
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5662 | h5662
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5663 | h5663
                            · linarith only [h2, h5547, h5655, h5663, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5665 | h5665
                              · linarith only [h2, h5547, h5655, h5661, h5665, hlam]
                              · rcases h1bigk with h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c | h5667c
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h5656, h5662, hc01, hlam, hphi, ht0b, ht5b, p5667_1, u5ehi3]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h5653, h5656, h5662, hc01, hlam, hphi, ht0b, ht5b, p5667_1, u5ehi3]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  rcases p5667_3 (m.d 0 1) (by simp) with h5671 | h5671
                                  · rcases p5667_3 (m.d 1 2) (by simp) with h5672 | h5672
                                    · linarith only [h0, h5672, hlam]
                                    · linarith only [h5655, h5672, hlam]
                                  · linarith only [h5671, hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  rcases p5667_3 (m.d 0 1) (by simp) with h5676 | h5676
                                  · rcases p5667_3 (m.d 1 2) (by simp) with h5677 | h5677
                                    · linarith only [h0, h5677, hlam]
                                    · linarith only [h5656, h5677, hlam]
                                  · linarith only [h5676, hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h0, hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h5653, hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  rcases p5667_3 (m.d 0 1) (by simp) with h5684 | h5684
                                  · rcases p5667_3 (m.d 1 2) (by simp) with h5685 | h5685
                                    · rcases p5667_3 (m.d 1 3) (by simp) with h5686 | h5686
                                      · rcases p5667_3 (m.d 1 4) (by simp) with h5687 | h5687
                                        · linarith only [h5655, h5687, hlam]
                                        · rcases p5667_3 (m.d 1 5) (by simp) with h5689 | h5689
                                          · linarith only [h5656, h5689, hlam]
                                          · linarith only [h5659, h5689, hlam]
                                      · linarith only [h5657, h5686, hlam]
                                    · linarith only [h5655, h5685, hlam]
                                  · linarith only [h2, h5684, hlam]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h0, h4, h5656, h5662, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5667_1, u5ehi3]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h1, hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h1, h5655, h5661, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5667_1]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  rcases p5667_3 (m.d 0 1) (by simp) with h5699 | h5699
                                  · rcases p5667_3 (m.d 1 2) (by simp) with h5700 | h5700
                                    · linarith only [h5653, h5700, hlam]
                                    · linarith only [h5655, h5700, hlam]
                                  · linarith only [h2, h5699, hlam]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h1, h5656, h5662, hc01, hlam, hphi, ht0b, ht5b, p5667_1, u5ehi3]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h2, hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h5655, hlam, p5667_1]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h5657, hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h5659, hlam, p5667_1]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h3, hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h5656, hlam, p5667_1]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [h5658, hlam, p5667_0]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  rcases p5667_3 (m.d 0 1) (by simp) with h5713 | h5713
                                  · rcases p5667_3 (m.d 1 2) (by simp) with h5714 | h5714
                                    · rcases p5667_3 (m.d 1 3) (by simp) with h5715 | h5715
                                      · rcases p5667_3 (m.d 1 4) (by simp) with h5716 | h5716
                                        · linarith only [h5659, h5716, hlam]
                                        · rcases p5667_3 (m.d 1 5) (by simp) with h5718 | h5718
                                          · rcases h1emax with h5719 | h5719 | h5719 | h5719 | h5719
                                            · linarith only [h0, h5655, h5656, h5661, h5719, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5667_1]
                                            · linarith only [h5655, h5656, h5661, h5719, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5667_1]
                                            · linarith only [h5653, h5655, h5656, h5661, h5719, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5667_1]
                                            · rcases h3bigk with h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c | h5723c
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h1, h5653, h5655, h5656, h5661, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5667_1, p5723_1]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h4, hlam, p5723_1]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                rcases p5723_3 (m.d 0 3) (by simp) with h5727 | h5727
                                                · rcases p5723_3 (m.d 1 3) (by simp) with h5728 | h5728
                                                  · linarith only [h1, h5728, hlam]
                                                  · linarith only [h5657, h5728, hlam]
                                                · linarith only [h5727, hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                rcases p5723_3 (m.d 0 3) (by simp) with h5732 | h5732
                                                · rcases p5723_3 (m.d 1 3) (by simp) with h5733 | h5733
                                                  · linarith only [h1, h5733, hlam]
                                                  · linarith only [h5658, h5733, hlam]
                                                · linarith only [h5732, hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h1, hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h5653, hlam, p5723_1]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                rcases p5723_3 (m.d 0 3) (by simp) with h5740 | h5740
                                                · rcases p5723_3 (m.d 1 3) (by simp) with h5741 | h5741
                                                  · rcases p5723_3 (m.d 2 3) (by simp) with h5742 | h5742
                                                    · rcases p5723_3 (m.d 3 4) (by simp) with h5743 | h5743
                                                      · linarith only [h5743, hlam, p5723_0]
                                                      · rcases p5723_3 (m.d 3 5) (by simp) with h5745 | h5745
                                                        · linarith only [h5658, h5745, hlam]
                                                        · linarith only [h5665, h5745, hlam]
                                                    · linarith only [h5661, h5742, hlam]
                                                  · linarith only [h5741, hlam, p5723_0]
                                                · linarith only [h5545, h5740, hlam]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p5723_1, u5ehi3]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h3, h4, h5544, h5655, h5661, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5667_1, p5723_1]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h5653, h5655, h5656, h5661, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5667_1, p5723_1]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h3, h4, h5544, h5655, h5661, hlam, p5667_1, p5723_2]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                rcases p5723_3 (m.d 0 3) (by simp) with h5756 | h5756
                                                · linarith only [h4, h5756, hlam]
                                                · linarith only [h5546, h5756, hlam]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h5545, hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h5657, hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h5661, hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h5665, hlam, p5723_1]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h5546, hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h5658, hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h5662, hlam, p5723_0]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [h4, h5544, h5662, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5723_1]
                                              · have p5723_0 := h5723c.1
                                                have p5723_1 := h5723c.2.1
                                                have p5723_2 := h5723c.2.2.1
                                                have p5723_3 := h5723c.2.2.2
                                                linarith only [hlam, p5723_0]
                                            · linarith only [h5655, h5661, h5719, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5667_1]
                                          · linarith only [h5659, h5718, hlam]
                                      · linarith only [h5657, h5715, hlam]
                                    · linarith only [h5655, h5714, hlam]
                                  · linarith only [h2, h5713, hlam]
                                · have p5667_0 := h5667c.1
                                  have p5667_1 := h5667c.2.1
                                  have p5667_2 := h5667c.2.2.1
                                  have p5667_3 := h5667c.2.2.2
                                  linarith only [hlam, p5667_0]
                          · linarith only [h0, h4, h5656, h5662, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h4, h5656, h5661, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h5546, h5653, h5656, h5658, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · linarith only [h4, h5545, h5653, h5656, h5657, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h4, h5544, h5656, hc12, hc23, hlam, hphi]
              · linarith only [h4, h5543, h5655, hc12, hc23, hlam, hphi]
        · linarith only [h4, h5544, h5546, hlam]
      · linarith only [h4, h5543, h5545, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5783 | h5783
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5784 | h5784
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5785 | h5785
          · linarith only [h5543, h5544, h5785, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5787 | h5787
            · linarith only [h0, h4, h5787, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5789 | h5789
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5790 | h5790
                · linarith only [h0, h5544, h5790, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5792 | h5792
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5793 | h5793
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5794 | h5794
                      · linarith only [h2, h5785, h5794, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5796 | h5796
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5797 | h5797
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5798 | h5798
                            · linarith only [h0, h5785, h5789, h5798, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5800 | h5800
                              · linarith only [h0, h5544, h5789, h5796, h5798, h5800, hlam]
                              · rcases h1bigk with h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  rcases p5802_3 (m.d 0 1) (by simp) with h5804 | h5804
                                  · rcases p5802_3 (m.d 1 2) (by simp) with h5805 | h5805
                                    · linarith only [h5805, hlam, p5802_0]
                                    · rcases p5802_3 (m.d 1 3) (by simp) with h5807 | h5807
                                      · linarith only [h1, h5807, hlam]
                                      · linarith only [h5787, h5807, hlam]
                                  · linarith only [h5804, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h5793, hc01, hlam, hphi, ht0b, ht5b, p5802_1, u5ehi3]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  rcases p5802_3 (m.d 0 1) (by simp) with h5812 | h5812
                                  · rcases p5802_3 (m.d 1 2) (by simp) with h5813 | h5813
                                    · linarith only [h0, h5813, hlam]
                                    · linarith only [h5789, h5813, hlam]
                                  · linarith only [h5812, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  rcases p5802_3 (m.d 0 1) (by simp) with h5817 | h5817
                                  · rcases p5802_3 (m.d 1 2) (by simp) with h5818 | h5818
                                    · linarith only [h0, h5818, hlam]
                                    · rcases p5802_3 (m.d 1 3) (by simp) with h5820 | h5820
                                      · linarith only [h1, h5820, hlam]
                                      · linarith only [h5793, h5820, hlam]
                                  · linarith only [h5817, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h0, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h5787, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h0, h5544, h5789, h5796, h5798, hc34, hc45, hlam, hphi, p5802_1]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h5790, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h1, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h1, h5789, h5796, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5802_1]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  rcases p5802_3 (m.d 0 1) (by simp) with h5832 | h5832
                                  · rcases p5802_3 (m.d 1 2) (by simp) with h5833 | h5833
                                    · linarith only [h5787, h5833, hlam]
                                    · linarith only [h5789, h5833, hlam]
                                  · linarith only [h2, h5832, hlam]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p5802_1, u5ehi1]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h2, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h5789, hlam, p5802_1]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h5792, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h5794, hlam, p5802_1]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h3, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h3, h5789, h5796, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5802_1]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [h5793, hlam, p5802_0]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  rcases p5802_3 (m.d 0 1) (by simp) with h5846 | h5846
                                  · rcases p5802_3 (m.d 1 2) (by simp) with h5847 | h5847
                                    · linarith only [h5790, h5847, hlam]
                                    · linarith only [h5789, h5847, hlam]
                                  · linarith only [h2, h5846, hlam]
                                · have p5802_0 := h5802c.1
                                  have p5802_1 := h5802c.2.1
                                  have p5802_2 := h5802c.2.2.1
                                  have p5802_3 := h5802c.2.2.2
                                  linarith only [hlam, p5802_0]
                          · linarith only [h4, h5784, h5797, hlam]
                        · linarith only [h4, h5783, h5796, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5854 | h5854
                      · linarith only [h2, h5785, h5854, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5856 | h5856
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5857 | h5857
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5858 | h5858
                            · linarith only [h5543, h5544, h5785, h5858, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5860 | h5860
                              · linarith only [h4, h5544, h5784, h5787, h5789, h5793, h5856, h5858, h5860, hc02, hc23, hlam, hphi]
                              · rcases h1bigk with h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c | h5862c
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  rcases p5862_3 (m.d 0 1) (by simp) with h5864 | h5864
                                  · rcases p5862_3 (m.d 1 2) (by simp) with h5865 | h5865
                                    · linarith only [h5865, hlam, p5862_0]
                                    · rcases p5862_3 (m.d 1 3) (by simp) with h5867 | h5867
                                      · linarith only [h1, h5867, hlam]
                                      · linarith only [h5787, h5867, hlam]
                                  · linarith only [h5864, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  rcases p5862_3 (m.d 0 1) (by simp) with h5871 | h5871
                                  · rcases p5862_3 (m.d 1 2) (by simp) with h5872 | h5872
                                    · linarith only [h0, h5872, hlam]
                                    · rcases p5862_3 (m.d 1 3) (by simp) with h5874 | h5874
                                      · linarith only [h5874, hlam, p5862_0]
                                      · rcases p5862_3 (m.d 1 4) (by simp) with h5876 | h5876
                                        · linarith only [h2, h5876, hlam]
                                        · rcases p5862_3 (m.d 1 5) (by simp) with h5878 | h5878
                                          · linarith only [h3, h5878, hlam]
                                          · linarith only [h5793, h5878, hlam]
                                  · linarith only [h5871, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  rcases p5862_3 (m.d 0 1) (by simp) with h5882 | h5882
                                  · rcases p5862_3 (m.d 1 2) (by simp) with h5883 | h5883
                                    · linarith only [h0, h5883, hlam]
                                    · linarith only [h5789, h5883, hlam]
                                  · linarith only [h5882, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  rcases p5862_3 (m.d 0 1) (by simp) with h5887 | h5887
                                  · rcases p5862_3 (m.d 1 2) (by simp) with h5888 | h5888
                                    · linarith only [h0, h5888, hlam]
                                    · rcases p5862_3 (m.d 1 3) (by simp) with h5890 | h5890
                                      · linarith only [h1, h5890, hlam]
                                      · rcases p5862_3 (m.d 1 4) (by simp) with h5892 | h5892
                                        · linarith only [h2, h5892, hlam]
                                        · rcases p5862_3 (m.d 1 5) (by simp) with h5894 | h5894
                                          · linarith only [h5894, hlam, p5862_0]
                                          · rcases h1emax with h5896 | h5896 | h5896 | h5896 | h5896
                                            · linarith only [h5896, hlam, hphi, ht01, ht0b, ht5b, p5862_1, u5ehi1]
                                            · rcases h3bigk with h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c | h5898c
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                rcases p5898_3 (m.d 0 3) (by simp) with h5900 | h5900
                                                · rcases p5898_3 (m.d 1 3) (by simp) with h5901 | h5901
                                                  · linarith only [h1, h5901, hlam]
                                                  · rcases p5898_3 (m.d 2 3) (by simp) with h5903 | h5903
                                                    · rcases p5898_3 (m.d 3 4) (by simp) with h5904 | h5904
                                                      · linarith only [h5783, h5904, hlam]
                                                      · rcases p5898_3 (m.d 3 5) (by simp) with h5906 | h5906
                                                        · linarith only [h5784, h5906, hlam]
                                                        · linarith only [h5793, h5906, hlam]
                                                    · linarith only [h5787, h5903, hlam]
                                                · linarith only [h1, h5900, hlam]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h4, hlam, p5898_1]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5784, h5787, h5789, h5793, h5856, hlam, p5898_2]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h4, h5787, h5789, h5793, h5856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5898_1]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h1, hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5787, hlam, p5898_1]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5544, h5784, h5793, h5858, hc34, hc45, hlam, hphi, p5898_1]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5793, hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5784, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5898_1, u5ehi3]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                rcases p5898_3 (m.d 0 3) (by simp) with h5920 | h5920
                                                · linarith only [h4, h5920, hlam]
                                                · linarith only [h1, h5920, hlam]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h4, h5784, h5787, h5789, h5793, h5856, hlam, p5898_2]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5787, h5789, h5793, h5856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5898_1]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5783, hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5792, hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5856, hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5860, hlam, p5898_1]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5784, hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5784, h5787, h5789, h5856, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5898_1]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [h5857, hlam, p5898_0]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                rcases p5898_3 (m.d 0 3) (by simp) with h5934 | h5934
                                                · rcases p5898_3 (m.d 1 3) (by simp) with h5935 | h5935
                                                  · linarith only [h5793, h5935, hlam]
                                                  · linarith only [h5792, h5935, hlam]
                                                · linarith only [h5783, h5934, hlam]
                                              · have p5898_0 := h5898c.1
                                                have p5898_1 := h5898c.2.1
                                                have p5898_2 := h5898c.2.2.1
                                                have p5898_3 := h5898c.2.2.2
                                                linarith only [hlam, p5898_0]
                                            · rcases h3bigk with h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                rcases p5940_3 (m.d 0 3) (by simp) with h5942 | h5942
                                                · rcases p5940_3 (m.d 1 3) (by simp) with h5943 | h5943
                                                  · linarith only [h1, h5943, hlam]
                                                  · rcases p5940_3 (m.d 2 3) (by simp) with h5945 | h5945
                                                    · rcases p5940_3 (m.d 3 4) (by simp) with h5946 | h5946
                                                      · linarith only [h5783, h5946, hlam]
                                                      · rcases p5940_3 (m.d 3 5) (by simp) with h5948 | h5948
                                                        · linarith only [h5784, h5948, hlam]
                                                        · linarith only [h5793, h5948, hlam]
                                                    · linarith only [h5787, h5945, hlam]
                                                · linarith only [h1, h5942, hlam]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h4, hlam, p5940_1]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5784, h5787, h5789, h5793, h5856, hlam, p5940_2]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5787, h5789, h5793, h5856, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5940_1]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h1, hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5787, hlam, p5940_1]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h4, h5784, h5793, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5940_1]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5793, hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5784, h5793, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5940_1]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                rcases p5940_3 (m.d 0 3) (by simp) with h5962 | h5962
                                                · linarith only [h4, h5962, hlam]
                                                · linarith only [h1, h5962, hlam]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h4, h5784, h5787, h5789, h5793, h5856, hlam, p5940_2]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5787, h5789, h5793, h5856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5940_1]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5783, hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5792, hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5856, hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5860, hlam, p5940_1]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5784, hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5784, h5787, h5789, h5856, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5940_1]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [h5857, hlam, p5940_0]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                rcases p5940_3 (m.d 0 3) (by simp) with h5976 | h5976
                                                · rcases p5940_3 (m.d 1 3) (by simp) with h5977 | h5977
                                                  · linarith only [h5793, h5977, hlam]
                                                  · linarith only [h5792, h5977, hlam]
                                                · linarith only [h5783, h5976, hlam]
                                              · have p5940_0 := h5940c.1
                                                have p5940_1 := h5940c.2.1
                                                have p5940_2 := h5940c.2.2.1
                                                have p5940_3 := h5940c.2.2.2
                                                linarith only [hlam, p5940_0]
                                            · rcases h3bigk with h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c | h5982c
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                rcases p5982_3 (m.d 0 3) (by simp) with h5984 | h5984
                                                · rcases p5982_3 (m.d 1 3) (by simp) with h5985 | h5985
                                                  · linarith only [h1, h5985, hlam]
                                                  · rcases p5982_3 (m.d 2 3) (by simp) with h5987 | h5987
                                                    · rcases p5982_3 (m.d 3 4) (by simp) with h5988 | h5988
                                                      · linarith only [h5783, h5988, hlam]
                                                      · rcases p5982_3 (m.d 3 5) (by simp) with h5990 | h5990
                                                        · linarith only [h5784, h5990, hlam]
                                                        · linarith only [h5793, h5990, hlam]
                                                    · linarith only [h5787, h5987, hlam]
                                                · linarith only [h1, h5984, hlam]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h4, hlam, p5982_1]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5784, h5787, h5789, h5793, h5856, hlam, p5982_2]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5787, h5789, h5793, h5856, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5982_1]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h1, hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5787, hlam, p5982_1]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h4, h5784, h5793, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5982_1]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5793, hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5784, h5793, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5982_1]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                rcases p5982_3 (m.d 0 3) (by simp) with h6004 | h6004
                                                · linarith only [h4, h6004, hlam]
                                                · linarith only [h1, h6004, hlam]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h4, h5784, h5787, h5789, h5793, h5856, hlam, p5982_2]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5787, h5789, h5793, h5856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5982_1]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5783, hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5792, hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5856, hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5860, hlam, p5982_1]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5784, hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5784, h5787, h5789, h5856, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5982_1]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [h5857, hlam, p5982_0]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                rcases p5982_3 (m.d 0 3) (by simp) with h6018 | h6018
                                                · rcases p5982_3 (m.d 1 3) (by simp) with h6019 | h6019
                                                  · linarith only [h5793, h6019, hlam]
                                                  · linarith only [h5792, h6019, hlam]
                                                · linarith only [h5783, h6018, hlam]
                                              · have p5982_0 := h5982c.1
                                                have p5982_1 := h5982c.2.1
                                                have p5982_2 := h5982c.2.2.1
                                                have p5982_3 := h5982c.2.2.2
                                                linarith only [hlam, p5982_0]
                                            · rcases h3bigk with h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c | h6024c
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                rcases p6024_3 (m.d 0 3) (by simp) with h6026 | h6026
                                                · rcases p6024_3 (m.d 1 3) (by simp) with h6027 | h6027
                                                  · linarith only [h1, h6027, hlam]
                                                  · rcases p6024_3 (m.d 2 3) (by simp) with h6029 | h6029
                                                    · rcases p6024_3 (m.d 3 4) (by simp) with h6030 | h6030
                                                      · linarith only [h5783, h6030, hlam]
                                                      · rcases p6024_3 (m.d 3 5) (by simp) with h6032 | h6032
                                                        · linarith only [h5784, h6032, hlam]
                                                        · linarith only [h5793, h6032, hlam]
                                                    · linarith only [h5787, h6029, hlam]
                                                · linarith only [h1, h6026, hlam]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h4, hlam, p6024_1]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5784, h5787, h5789, h5793, h5856, hlam, p6024_2]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5787, h5789, h5793, h5856, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6024_1]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h1, hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5787, hlam, p6024_1]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h4, h5784, h5793, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6024_1]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5793, hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5784, h5793, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p6024_1]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                rcases p6024_3 (m.d 0 3) (by simp) with h6046 | h6046
                                                · linarith only [h4, h6046, hlam]
                                                · linarith only [h1, h6046, hlam]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h4, h5784, h5787, h5789, h5793, h5856, hlam, p6024_2]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5787, h5789, h5793, h5856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6024_1]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5783, hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5792, hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5856, hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5860, hlam, p6024_1]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5784, hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5784, h5787, h5789, h5856, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6024_1]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [h5857, hlam, p6024_0]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                rcases p6024_3 (m.d 0 3) (by simp) with h6060 | h6060
                                                · rcases p6024_3 (m.d 1 3) (by simp) with h6061 | h6061
                                                  · linarith only [h5793, h6061, hlam]
                                                  · linarith only [h5792, h6061, hlam]
                                                · linarith only [h5783, h6060, hlam]
                                              · have p6024_0 := h6024c.1
                                                have p6024_1 := h6024c.2.1
                                                have p6024_2 := h6024c.2.2.1
                                                have p6024_3 := h6024c.2.2.2
                                                linarith only [hlam, p6024_0]
                                  · linarith only [h5887, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h0, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h5787, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h0, h5544, h5858, hc14, hc45, hlam, hphi, p5862_1]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h5790, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h1, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h1, h5789, h5856, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5862_1]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h4, h5784, h5789, h5793, h5856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5862_1]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h5793, hlam, p5862_1]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h2, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h5789, hlam, p5862_1]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h5792, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h5854, hlam, p5862_1]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h3, hlam, p5862_0]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h3, h5789, h5856, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5862_1]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [h4, h5784, h5787, h5789, h5793, h5856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5862_1]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  rcases p5862_3 (m.d 0 1) (by simp) with h6085 | h6085
                                  · rcases p5862_3 (m.d 1 2) (by simp) with h6086 | h6086
                                    · linarith only [h5790, h6086, hlam]
                                    · linarith only [h5789, h6086, hlam]
                                  · linarith only [h2, h6085, hlam]
                                · have p5862_0 := h5862c.1
                                  have p5862_1 := h5862c.2.1
                                  have p5862_2 := h5862c.2.2.1
                                  have p5862_3 := h5862c.2.2.2
                                  linarith only [hlam, p5862_0]
                          · linarith only [h4, h5784, h5857, hlam]
                        · linarith only [h4, h5783, h5856, hlam]
                  · linarith only [h5783, h5785, h5787, h5789, h5792, hc24, hc45, hlam, hphi]
              · linarith only [h4, h5543, h5789, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6095 | h6095
          · linarith only [h5543, h5544, h6095, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6097 | h6097
            · linarith only [h0, h4, h5543, h6097, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6099 | h6099
              · rcases m.htr 1 2 5 (by decide) (by decide) with h6100 | h6100
                · linarith only [h0, h5544, h6100, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6102 | h6102
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6103 | h6103
                    · linarith only [h1, h5784, h6103, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6105 | h6105
                      · linarith only [h2, h4, h5543, h5784, h6095, h6105, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6107 | h6107
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6108 | h6108
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6109 | h6109
                            · linarith only [h0, h4, h5784, h6095, h6099, h6108, h6109, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6111 | h6111
                              · linarith only [h4, h5543, h5784, h6107, h6108, h6109, h6111, hlam]
                              · rcases h1bigk with h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  rcases p6113_3 (m.d 0 1) (by simp) with h6115 | h6115
                                  · rcases p6113_3 (m.d 1 2) (by simp) with h6116 | h6116
                                    · linarith only [h6116, hlam, p6113_0]
                                    · rcases p6113_3 (m.d 1 3) (by simp) with h6118 | h6118
                                      · linarith only [h1, h6118, hlam]
                                      · linarith only [h6097, h6118, hlam]
                                  · linarith only [h6115, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  rcases p6113_3 (m.d 0 1) (by simp) with h6122 | h6122
                                  · rcases p6113_3 (m.d 1 2) (by simp) with h6123 | h6123
                                    · linarith only [h0, h6123, hlam]
                                    · rcases p6113_3 (m.d 1 3) (by simp) with h6125 | h6125
                                      · linarith only [h6125, hlam, p6113_0]
                                      · rcases p6113_3 (m.d 1 4) (by simp) with h6127 | h6127
                                        · linarith only [h2, h6127, hlam]
                                        · rcases p6113_3 (m.d 1 5) (by simp) with h6129 | h6129
                                          · linarith only [h3, h6129, hlam]
                                          · linarith only [h6103, h6129, hlam]
                                  · linarith only [h6122, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  rcases p6113_3 (m.d 0 1) (by simp) with h6133 | h6133
                                  · rcases p6113_3 (m.d 1 2) (by simp) with h6134 | h6134
                                    · linarith only [h0, h6134, hlam]
                                    · linarith only [h6099, h6134, hlam]
                                  · linarith only [h6133, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  rcases p6113_3 (m.d 0 1) (by simp) with h6138 | h6138
                                  · rcases p6113_3 (m.d 1 2) (by simp) with h6139 | h6139
                                    · linarith only [h0, h6139, hlam]
                                    · rcases p6113_3 (m.d 1 3) (by simp) with h6141 | h6141
                                      · linarith only [h1, h6141, hlam]
                                      · rcases p6113_3 (m.d 1 4) (by simp) with h6143 | h6143
                                        · linarith only [h2, h6143, hlam]
                                        · rcases p6113_3 (m.d 1 5) (by simp) with h6145 | h6145
                                          · linarith only [h6145, hlam, p6113_0]
                                          · rcases h1emax with h6147 | h6147 | h6147 | h6147 | h6147
                                            · linarith only [h6097, h6103, h6147, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6113_1]
                                            · rcases h3bigk with h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h5784, h6097, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6149_1]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h4, hlam, p6149_1]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h5784, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6149_1]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h5784, hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h1, hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h6097, hlam, p6149_1]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h6103, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6113_1, p6149_1]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h6103, hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                rcases p6149_3 (m.d 0 3) (by simp) with h6160 | h6160
                                                · linarith only [h4, h6160, hlam]
                                                · rcases p6149_3 (m.d 1 3) (by simp) with h6162 | h6162
                                                  · linarith only [h6097, h6162, hlam]
                                                  · rcases p6149_3 (m.d 2 3) (by simp) with h6164 | h6164
                                                    · rcases p6149_3 (m.d 3 4) (by simp) with h6165 | h6165
                                                      · linarith only [h6107, h6165, hlam]
                                                      · rcases p6149_3 (m.d 3 5) (by simp) with h6167 | h6167
                                                        · linarith only [h6108, h6167, hlam]
                                                        · linarith only [h5784, h6167, hlam]
                                                    · linarith only [h4, h6164, hlam]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                rcases p6149_3 (m.d 0 3) (by simp) with h6171 | h6171
                                                · linarith only [h4, h6171, hlam]
                                                · linarith only [h1, h6171, hlam]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h0, h4, h5784, h6099, h6107, h6108, hlam, p6149_2]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h4, h5784, hc02, hc23, hlam, hphi, p6149_1]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h5783, hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h6102, hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h6107, hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h6111, hlam, p6149_1]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h0, h4, h6099, h6107, h6108, h6109, hc34, hc45, hlam, hphi, p6149_1]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h6097, h6099, h6107, h6108, h6109, hc34, hc45, hlam, hphi, p6149_1]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [h6108, hlam, p6149_0]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                rcases p6149_3 (m.d 0 3) (by simp) with h6185 | h6185
                                                · linarith only [h5784, h6185, hlam]
                                                · linarith only [h5783, h6185, hlam]
                                              · have p6149_0 := h6149c.1
                                                have p6149_1 := h6149c.2.1
                                                have p6149_2 := h6149c.2.2.1
                                                have p6149_3 := h6149c.2.2.2
                                                linarith only [hlam, p6149_0]
                                            · rcases h3bigk with h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h5544, h5784, h6097, h6099, h6107, h6109, hc34, hc45, hlam, hphi, p6189_1]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h4, hlam, p6189_1]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h5784, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6189_1]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h5784, hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h1, hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h6097, hlam, p6189_1]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h1, h5784, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6189_1]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h6103, hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                rcases p6189_3 (m.d 0 3) (by simp) with h6200 | h6200
                                                · linarith only [h4, h6200, hlam]
                                                · rcases p6189_3 (m.d 1 3) (by simp) with h6202 | h6202
                                                  · linarith only [h6097, h6202, hlam]
                                                  · rcases p6189_3 (m.d 2 3) (by simp) with h6204 | h6204
                                                    · rcases p6189_3 (m.d 3 4) (by simp) with h6205 | h6205
                                                      · linarith only [h6107, h6205, hlam]
                                                      · rcases p6189_3 (m.d 3 5) (by simp) with h6207 | h6207
                                                        · linarith only [h6108, h6207, hlam]
                                                        · linarith only [h5784, h6207, hlam]
                                                    · linarith only [h4, h6204, hlam]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                rcases p6189_3 (m.d 0 3) (by simp) with h6211 | h6211
                                                · linarith only [h4, h6211, hlam]
                                                · linarith only [h1, h6211, hlam]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h0, h4, h5784, h6099, h6107, h6108, hlam, p6189_2]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h4, h5784, hc02, hc23, hlam, hphi, p6189_1]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h5783, hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h6102, hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h6107, hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h6111, hlam, p6189_1]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h0, h4, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6189_1]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h6097, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6189_1]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [h6108, hlam, p6189_0]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                rcases p6189_3 (m.d 0 3) (by simp) with h6225 | h6225
                                                · linarith only [h5784, h6225, hlam]
                                                · linarith only [h5783, h6225, hlam]
                                              · have p6189_0 := h6189c.1
                                                have p6189_1 := h6189c.2.1
                                                have p6189_2 := h6189c.2.2.1
                                                have p6189_3 := h6189c.2.2.2
                                                linarith only [hlam, p6189_0]
                                            · rcases h3bigk with h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h5784, h6097, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6229_1]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h4, hlam, p6229_1]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h5784, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6229_1]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h5784, hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h1, hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h6097, hlam, p6229_1]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h1, h5784, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6229_1]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h6103, hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                rcases p6229_3 (m.d 0 3) (by simp) with h6240 | h6240
                                                · linarith only [h4, h6240, hlam]
                                                · rcases p6229_3 (m.d 1 3) (by simp) with h6242 | h6242
                                                  · linarith only [h6097, h6242, hlam]
                                                  · rcases p6229_3 (m.d 2 3) (by simp) with h6244 | h6244
                                                    · rcases p6229_3 (m.d 3 4) (by simp) with h6245 | h6245
                                                      · linarith only [h6107, h6245, hlam]
                                                      · rcases p6229_3 (m.d 3 5) (by simp) with h6247 | h6247
                                                        · linarith only [h6108, h6247, hlam]
                                                        · linarith only [h5784, h6247, hlam]
                                                    · linarith only [h4, h6244, hlam]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                rcases p6229_3 (m.d 0 3) (by simp) with h6251 | h6251
                                                · linarith only [h4, h6251, hlam]
                                                · linarith only [h1, h6251, hlam]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h0, h4, h5784, h6099, h6107, h6108, hlam, p6229_2]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h0, h4, h5784, h6099, h6107, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6229_1]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h5783, hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h6102, hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h6107, hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h6111, hlam, p6229_1]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h0, h4, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6229_1]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h6097, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6229_1]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [h6108, hlam, p6229_0]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                rcases p6229_3 (m.d 0 3) (by simp) with h6265 | h6265
                                                · linarith only [h5784, h6265, hlam]
                                                · linarith only [h5783, h6265, hlam]
                                              · have p6229_0 := h6229c.1
                                                have p6229_1 := h6229c.2.1
                                                have p6229_2 := h6229c.2.2.1
                                                have p6229_3 := h6229c.2.2.2
                                                linarith only [hlam, p6229_0]
                                            · rcases h3bigk with h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h5784, h6097, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6269_1]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h4, hlam, p6269_1]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h5784, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6269_1]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h5784, hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h1, hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h6097, hlam, p6269_1]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h1, h5784, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6269_1]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h6103, hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                rcases p6269_3 (m.d 0 3) (by simp) with h6280 | h6280
                                                · linarith only [h4, h6280, hlam]
                                                · rcases p6269_3 (m.d 1 3) (by simp) with h6282 | h6282
                                                  · linarith only [h6097, h6282, hlam]
                                                  · rcases p6269_3 (m.d 2 3) (by simp) with h6284 | h6284
                                                    · rcases p6269_3 (m.d 3 4) (by simp) with h6285 | h6285
                                                      · linarith only [h6107, h6285, hlam]
                                                      · rcases p6269_3 (m.d 3 5) (by simp) with h6287 | h6287
                                                        · linarith only [h6108, h6287, hlam]
                                                        · linarith only [h5784, h6287, hlam]
                                                    · linarith only [h4, h6284, hlam]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                rcases p6269_3 (m.d 0 3) (by simp) with h6291 | h6291
                                                · linarith only [h4, h6291, hlam]
                                                · linarith only [h1, h6291, hlam]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h0, h4, h5784, h6099, h6107, h6108, hlam, p6269_2]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h4, h5784, hc02, hc23, hlam, hphi, p6269_1]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h5783, hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h6102, hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h6107, hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h6111, hlam, p6269_1]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h0, h4, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6269_1]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h6097, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6269_1]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [h6108, hlam, p6269_0]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                rcases p6269_3 (m.d 0 3) (by simp) with h6305 | h6305
                                                · linarith only [h5784, h6305, hlam]
                                                · linarith only [h5783, h6305, hlam]
                                              · have p6269_0 := h6269c.1
                                                have p6269_1 := h6269c.2.1
                                                have p6269_2 := h6269c.2.2.1
                                                have p6269_3 := h6269c.2.2.2
                                                linarith only [hlam, p6269_0]
                                  · linarith only [h6138, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h0, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h6097, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h0, h5544, h6099, h6107, h6109, hc34, hc45, hlam, hphi, p6113_1]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h6100, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h1, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h1, h5784, h6108, hc12, hc23, hlam, hphi, p6113_1]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h1, h5784, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6113_1]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h6103, hlam, p6113_1]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h2, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h6099, hlam, p6113_1]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h6102, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h6105, hlam, p6113_1]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h3, hlam, p6113_0]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h3, h5784, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6113_1]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [h3, h5784, h6097, h6099, h6107, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6113_1]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  rcases p6113_3 (m.d 0 1) (by simp) with h6328 | h6328
                                  · rcases p6113_3 (m.d 1 2) (by simp) with h6329 | h6329
                                    · linarith only [h6100, h6329, hlam]
                                    · linarith only [h6099, h6329, hlam]
                                  · linarith only [h2, h6328, hlam]
                                · have p6113_0 := h6113c.1
                                  have p6113_1 := h6113c.2.1
                                  have p6113_2 := h6113c.2.2.1
                                  have p6113_3 := h6113c.2.2.2
                                  linarith only [hlam, p6113_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6334 | h6334
                            · linarith only [h0, h6095, h6099, h6334, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6336 | h6336
                              · linarith only [h0, h4, h6099, h6107, h6108, h6334, h6336, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h0, h4, h6099, h6107, h6108, h6336, hc34, hc45, hlam, hphi]
                        · linarith only [h0, h4, h5783, h6099, h6107, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h5783, h5784, h6102, hc13, hc35, hlam, hphi]
              · linarith only [h4, h5543, h6099, hc12, hc23, hlam, hphi]
      · linarith only [h4, h5543, h5783, hlam]
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s10 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5543

set_option maxHeartbeats 19046000 in
set_option maxHeartbeats 19046000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s4 m hb1 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s9 m hb1 hb3 hb5 h0 h1 h2 h3 h4

end R2N4
