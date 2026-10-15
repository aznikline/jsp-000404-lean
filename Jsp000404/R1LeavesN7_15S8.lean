import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S5
import Jsp000404.R1LeavesN7_15S6
import Jsp000404.R1LeavesN7_15S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10174000 in
set_option maxHeartbeats 10174000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3397 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3738 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h3969 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h4619 | h4619
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4620 | h4620
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4621 | h4621
      · linarith only [h0, h4, h4621, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4623 | h4623
        · linarith only [h0, h3397, h4623, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4625 | h4625
          · linarith only [h0, h3738, h4625, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4627 | h4627
            · linarith only [h1, h3969, h4619, h4627, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4629 | h4629
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4630 | h4630
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4631 | h4631
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4632 | h4632
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4633 | h4633
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4634 | h4634
                        · rcases h0bigk with h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c | h4635c
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [hlam, p4635_0]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            rcases p4635_3 (m.d 0 1) (by simp) with h4637 | h4637
                            · rcases p4635_3 (m.d 0 2) (by simp) with h4638 | h4638
                              · linarith only [h0, h4638, hlam]
                              · rcases p4635_3 (m.d 0 3) (by simp) with h4640 | h4640
                                · linarith only [h1, h4640, hlam]
                                · linarith only [h4, h4640, hlam]
                            · linarith only [h0, h4637, hlam]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h1, h4629, h4634, hc01, hc45, hlam, hphi, ht0b, ht5b, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h1, h3969, h4629, h4634, hc01, hc45, hlam, hphi, ht0b, ht5b, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            rcases p4635_3 (m.d 0 1) (by simp) with h4646 | h4646
                            · rcases p4635_3 (m.d 0 2) (by simp) with h4647 | h4647
                              · linarith only [h0, h4647, hlam]
                              · rcases p4635_3 (m.d 0 3) (by simp) with h4649 | h4649
                                · linarith only [h1, h4649, hlam]
                                · linarith only [h4619, h4649, hlam]
                            · linarith only [h3, h4646, hlam]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h0, hlam, p4635_0]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [hlam, p4635_0]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h4, hlam, p4635_0]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h3397, hlam, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h3738, hlam, p4635_0]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h1, hlam, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [hlam, p4635_0]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h3969, hlam, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h0, h3738, h3969, h4631, hc12, hc23, hlam, hphi, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h2, hlam, p4635_0]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h0, h3969, h4631, hc12, hc23, hlam, hphi, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h3969, h4631, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [hlam, p4635_0]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h0, h3738, h3969, h4631, hc12, hc23, hlam, hphi, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h3, hlam, p4635_0]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h4619, hlam, p4635_0]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [h4620, hlam, p4635_1]
                          · have p4635_0 := h4635c.1
                            have p4635_1 := h4635c.2.1
                            have p4635_2 := h4635c.2.2.1
                            have p4635_3 := h4635c.2.2.2
                            linarith only [hlam, p4635_0]
                        · linarith only [h1, h3969, h4620, h4629, h4634, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h3, h3397, h3969, h4619, h4630, h4633, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h3969, h4629, h4631, h4632, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4676 | h4676
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4677 | h4677
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4678 | h4678
                        · rcases h0bigk with h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c | h4679c
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [hlam, p4679_0]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            rcases p4679_3 (m.d 0 1) (by simp) with h4681 | h4681
                            · rcases p4679_3 (m.d 0 2) (by simp) with h4682 | h4682
                              · linarith only [h0, h4682, hlam]
                              · rcases p4679_3 (m.d 0 3) (by simp) with h4684 | h4684
                                · linarith only [h1, h4684, hlam]
                                · linarith only [h4, h4684, hlam]
                            · linarith only [h0, h4681, hlam]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h1, h4629, h4678, hc01, hc45, hlam, hphi, ht0b, ht5b, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h1, h3969, h4629, h4678, hc01, hc45, hlam, hphi, ht0b, ht5b, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            rcases p4679_3 (m.d 0 1) (by simp) with h4690 | h4690
                            · rcases p4679_3 (m.d 0 2) (by simp) with h4691 | h4691
                              · linarith only [h0, h4691, hlam]
                              · rcases p4679_3 (m.d 0 3) (by simp) with h4693 | h4693
                                · linarith only [h1, h4693, hlam]
                                · linarith only [h4619, h4693, hlam]
                            · linarith only [h3, h4690, hlam]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h0, hlam, p4679_0]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [hlam, p4679_0]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h4, hlam, p4679_0]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h3397, hlam, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h3738, hlam, p4679_0]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h1, hlam, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [hlam, p4679_0]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h3969, hlam, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h0, h3738, h4, h4631, hc12, hc34, hlam, hphi, ht23, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h2, hlam, p4679_0]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h0, h3969, hc12, hc34, hlam, hphi, ht23, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h3969, hc03, hc34, hlam, hphi, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [hlam, p4679_0]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h0, h3738, h3969, hc12, hc34, hlam, hphi, ht23, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h3, hlam, p4679_0]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h4619, hlam, p4679_0]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [h4620, hlam, p4679_1]
                          · have p4679_0 := h4679c.1
                            have p4679_1 := h4679c.2.1
                            have p4679_2 := h4679c.2.2.1
                            have p4679_3 := h4679c.2.2.2
                            linarith only [hlam, p4679_0]
                        · linarith only [h0, h4, h4631, h4678, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h1, h3397, h4, h4629, h4630, h4631, h4677, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h4, h4629, h4676, hlam]
                · linarith only [h4627, h4629, h4630, hlam]
              · linarith only [h3969, h4619, h4629, hc13, hc34, hlam, hphi]
    · linarith only [h3969, h4619, h4620, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4723 | h4723
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4724 | h4724
      · linarith only [h0, h4, h4724, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4726 | h4726
        · linarith only [h0, h3397, h4726, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4728 | h4728
          · linarith only [h0, h3738, h4728, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4730 | h4730
            · linarith only [h1, h3969, h4730, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4732 | h4732
              · linarith only [h1, h4619, h4732, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4734 | h4734
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4735 | h4735
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4736 | h4736
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4737 | h4737
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4738 | h4738
                        · rcases h0bigk with h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [hlam, p4739_0]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            rcases p4739_3 (m.d 0 1) (by simp) with h4741 | h4741
                            · rcases p4739_3 (m.d 0 2) (by simp) with h4742 | h4742
                              · linarith only [h0, h4742, hlam]
                              · rcases p4739_3 (m.d 0 3) (by simp) with h4744 | h4744
                                · linarith only [h1, h4744, hlam]
                                · linarith only [h4, h4744, hlam]
                            · linarith only [h0, h4741, hlam]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            rcases p4739_3 (m.d 0 1) (by simp) with h4748 | h4748
                            · rcases p4739_3 (m.d 0 2) (by simp) with h4749 | h4749
                              · linarith only [h0, h4749, hlam]
                              · rcases p4739_3 (m.d 0 3) (by simp) with h4751 | h4751
                                · linarith only [h1, h4751, hlam]
                                · rcases p4739_3 (m.d 0 4) (by simp) with h4753 | h4753
                                  · linarith only [h2, h4753, hlam]
                                  · linarith only [h3969, h4753, hlam]
                            · linarith only [h1, h4748, hlam]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h2, h4734, hc01, hc45, hlam, hphi, ht0b, ht5b, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            rcases p4739_3 (m.d 0 1) (by simp) with h4758 | h4758
                            · rcases p4739_3 (m.d 0 2) (by simp) with h4759 | h4759
                              · linarith only [h0, h4759, hlam]
                              · rcases p4739_3 (m.d 0 3) (by simp) with h4761 | h4761
                                · linarith only [h1, h4761, hlam]
                                · rcases p4739_3 (m.d 0 4) (by simp) with h4763 | h4763
                                  · linarith only [h2, h4763, hlam]
                                  · linarith only [h4723, h4763, hlam]
                            · linarith only [h3, h4758, hlam]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h0, hlam, p4739_0]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [hlam, p4739_0]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h4, hlam, p4739_0]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h3397, hlam, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h3738, hlam, p4739_0]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h1, hlam, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h0, h4619, h4736, hc12, hc25, hlam, hphi, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [hlam, p4739_0]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h3969, hlam, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h4619, hlam, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h2, hlam, p4739_0]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h0, h3397, h4735, hc12, hc23, hlam, hphi, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h0, h3397, h4, h4735, hc12, hc23, hlam, hphi, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [hlam, p4739_0]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h0, h3397, h4, h4619, h4735, hc12, hc23, hlam, hphi, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h3, hlam, p4739_0]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h0, h4, h4619, h4738, hc12, hc34, hlam, hphi, ht23, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [h4723, hlam, p4739_1]
                          · have p4739_0 := h4739c.1
                            have p4739_1 := h4739c.2.1
                            have p4739_2 := h4739c.2.2.1
                            have p4739_3 := h4739c.2.2.2
                            linarith only [hlam, p4739_0]
                        · linarith only [h2, h3969, h4734, h4738, hlam]
                      · linarith only [h0, h2, h3397, h4734, h4737, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h3969, h4, h4735, h4736, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4790 | h4790
                    · linarith only [h0, h4, h4619, h4735, h4790, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4792 | h4792
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4793 | h4793
                        · rcases h0bigk with h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [hlam, p4794_0]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            rcases p4794_3 (m.d 0 1) (by simp) with h4796 | h4796
                            · rcases p4794_3 (m.d 0 2) (by simp) with h4797 | h4797
                              · linarith only [h0, h4797, hlam]
                              · rcases p4794_3 (m.d 0 3) (by simp) with h4799 | h4799
                                · linarith only [h1, h4799, hlam]
                                · linarith only [h4, h4799, hlam]
                            · linarith only [h0, h4796, hlam]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            rcases p4794_3 (m.d 0 1) (by simp) with h4803 | h4803
                            · rcases p4794_3 (m.d 0 2) (by simp) with h4804 | h4804
                              · linarith only [h0, h4804, hlam]
                              · rcases p4794_3 (m.d 0 3) (by simp) with h4806 | h4806
                                · linarith only [h1, h4806, hlam]
                                · rcases p4794_3 (m.d 0 4) (by simp) with h4808 | h4808
                                  · linarith only [h2, h4808, hlam]
                                  · linarith only [h3969, h4808, hlam]
                            · linarith only [h1, h4803, hlam]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h2, h4734, hc01, hc45, hlam, hphi, ht0b, ht5b, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            rcases p4794_3 (m.d 0 1) (by simp) with h4813 | h4813
                            · rcases p4794_3 (m.d 0 2) (by simp) with h4814 | h4814
                              · linarith only [h0, h4814, hlam]
                              · rcases p4794_3 (m.d 0 3) (by simp) with h4816 | h4816
                                · linarith only [h1, h4816, hlam]
                                · rcases p4794_3 (m.d 0 4) (by simp) with h4818 | h4818
                                  · linarith only [h2, h4818, hlam]
                                  · linarith only [h4723, h4818, hlam]
                            · linarith only [h3, h4813, hlam]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h0, hlam, p4794_0]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [hlam, p4794_0]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h4, hlam, p4794_0]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h3397, hlam, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h3738, hlam, p4794_0]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h1, hlam, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h0, h4, h4790, h4793, hc12, hc34, hlam, hphi, ht23, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [hlam, p4794_0]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h3969, hlam, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h4619, hlam, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h2, hlam, p4794_0]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h0, h3397, h4735, hc12, hc34, hlam, hphi, ht23, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h3397, h4735, hc03, hc34, hlam, hphi, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [hlam, p4794_0]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h3, h3397, h4724, h4732, h4735, hc12, hc34, hlam, hphi, ht23, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h3, hlam, p4794_0]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h1, h4619, h4724, h4793, hc12, hc34, hlam, hphi, ht23, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [h4723, hlam, p4794_1]
                          · have p4794_0 := h4794c.1
                            have p4794_1 := h4794c.2.1
                            have p4794_2 := h4794c.2.2.1
                            have p4794_3 := h4794c.2.2.2
                            linarith only [hlam, p4794_0]
                        · linarith only [h2, h3397, h4734, h4735, h4793, hlam]
                      · linarith only [h3397, h4723, h4792, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4844 | h4844
                  · linarith only [h3969, h4723, h4724, h4730, h4734, h4844, hc12, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4846 | h4846
                    · linarith only [h1, h4619, h4724, h4844, h4846, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4848 | h4848
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4849 | h4849
                        · rcases h0bigk with h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c | h4850c
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [hlam, p4850_0]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            rcases p4850_3 (m.d 0 1) (by simp) with h4852 | h4852
                            · rcases p4850_3 (m.d 0 2) (by simp) with h4853 | h4853
                              · linarith only [h0, h4853, hlam]
                              · rcases p4850_3 (m.d 0 3) (by simp) with h4855 | h4855
                                · linarith only [h1, h4855, hlam]
                                · linarith only [h4, h4855, hlam]
                            · linarith only [h0, h4852, hlam]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            rcases p4850_3 (m.d 0 1) (by simp) with h4859 | h4859
                            · rcases p4850_3 (m.d 0 2) (by simp) with h4860 | h4860
                              · linarith only [h0, h4860, hlam]
                              · rcases p4850_3 (m.d 0 3) (by simp) with h4862 | h4862
                                · linarith only [h1, h4862, hlam]
                                · rcases p4850_3 (m.d 0 4) (by simp) with h4864 | h4864
                                  · linarith only [h2, h4864, hlam]
                                  · linarith only [h3969, h4864, hlam]
                            · linarith only [h1, h4859, hlam]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h4723, h4724, h4730, h4734, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h4723, h4724, h4730, h4734, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h0, hlam, p4850_0]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [hlam, p4850_0]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h4, hlam, p4850_0]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h3397, hlam, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h3738, hlam, p4850_0]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h1, hlam, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h0, h4, h4846, h4849, hc12, hc34, hlam, hphi, ht23, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [hlam, p4850_0]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h3969, hlam, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h4619, hlam, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h2, hlam, p4850_0]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h0, h3397, hc12, hc24, hlam, hphi, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h3969, hc03, hc34, hlam, hphi, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [hlam, p4850_0]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h0, h3738, h3969, hc12, hc34, hlam, hphi, ht23, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h3, hlam, p4850_0]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h1, h4619, h4724, h4849, hc12, hc34, hlam, hphi, ht23, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [h4723, hlam, p4850_1]
                          · have p4850_0 := h4850c.1
                            have p4850_1 := h4850c.2.1
                            have p4850_2 := h4850c.2.2.1
                            have p4850_3 := h4850c.2.2.2
                            linarith only [hlam, p4850_0]
                        · linarith only [h3397, h4723, h4844, h4849, hlam]
                      · linarith only [h3397, h4723, h4848, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4892 | h4892
      · linarith only [h0, h4, h4892, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4894 | h4894
        · linarith only [h0, h3397, h4894, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4896 | h4896
          · linarith only [h0, h3738, h4896, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4898 | h4898
            · linarith only [h1, h3969, h4898, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4900 | h4900
              · linarith only [h1, h4619, h4900, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4902 | h4902
                · linarith only [h2, h4723, h4902, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4904 | h4904
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4905 | h4905
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4906 | h4906
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4907 | h4907
                        · linarith only [h0, h3397, h4723, h4904, h4907, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h3969, h4, h4904, h4906, h4907, hc12, hc23, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4910 | h4910
                        · linarith only [h0, h3397, h4906, h4910, hc12, hc34, hlam, hphi, ht23]
                        · rcases h0bigk with h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c | h4912c
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [hlam, p4912_0]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            rcases p4912_3 (m.d 0 1) (by simp) with h4914 | h4914
                            · rcases p4912_3 (m.d 0 2) (by simp) with h4915 | h4915
                              · linarith only [h0, h4915, hlam]
                              · rcases p4912_3 (m.d 0 3) (by simp) with h4917 | h4917
                                · linarith only [h1, h4917, hlam]
                                · linarith only [h4, h4917, hlam]
                            · linarith only [h0, h4914, hlam]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            rcases p4912_3 (m.d 0 1) (by simp) with h4921 | h4921
                            · rcases p4912_3 (m.d 0 2) (by simp) with h4922 | h4922
                              · linarith only [h0, h4922, hlam]
                              · rcases p4912_3 (m.d 0 3) (by simp) with h4924 | h4924
                                · linarith only [h1, h4924, hlam]
                                · rcases p4912_3 (m.d 0 4) (by simp) with h4926 | h4926
                                  · linarith only [h2, h4926, hlam]
                                  · linarith only [h3969, h4926, hlam]
                            · linarith only [h1, h4921, hlam]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            rcases p4912_3 (m.d 0 1) (by simp) with h4930 | h4930
                            · rcases p4912_3 (m.d 0 2) (by simp) with h4931 | h4931
                              · linarith only [h0, h4931, hlam]
                              · rcases p4912_3 (m.d 0 3) (by simp) with h4933 | h4933
                                · linarith only [h1, h4933, hlam]
                                · rcases p4912_3 (m.d 0 4) (by simp) with h4935 | h4935
                                  · linarith only [h2, h4935, hlam]
                                  · rcases p4912_3 (m.d 0 5) (by simp) with h4937 | h4937
                                    · linarith only [h3, h4937, hlam]
                                    · linarith only [h4723, h4937, hlam]
                            · linarith only [h2, h4930, hlam]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            rcases p4912_3 (m.d 0 1) (by simp) with h4941 | h4941
                            · rcases p4912_3 (m.d 0 2) (by simp) with h4942 | h4942
                              · linarith only [h0, h4942, hlam]
                              · rcases p4912_3 (m.d 0 3) (by simp) with h4944 | h4944
                                · linarith only [h1, h4944, hlam]
                                · rcases p4912_3 (m.d 0 4) (by simp) with h4946 | h4946
                                  · linarith only [h2, h4946, hlam]
                                  · rcases p4912_3 (m.d 0 5) (by simp) with h4948 | h4948
                                    · linarith only [h3, h4948, hlam]
                                    · rcases h1bigk with h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h0, h3969, h4, h4723, hlam, p4912_1, p4950_2]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h1, h3969, h4723, hlam, p4912_1, p4950_2]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h2, h4723, hlam, p4912_1, p4950_2]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h3, hlam, p4912_1, p4950_2]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h0, hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h4892, hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h4894, hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h4896, hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h1, hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h1, h3969, h4723, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4912_1, p4950_1]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h4898, hlam, p4950_1]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h4900, hlam, p4950_1]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h2, hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h2, h4723, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4912_1, p4950_1]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h2, h4723, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4912_1, p4950_1]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h4902, hlam, p4950_1]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h3, hlam, p4950_0]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4912_1, p4950_1]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h3, h4892, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4912_1, p4950_1]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4912_1, p4950_1]
                                      · have p4950_0 := h4950c.1
                                        have p4950_1 := h4950c.2.1
                                        have p4950_2 := h4950c.2.2.1
                                        have p4950_3 := h4950c.2.2.2
                                        linarith only [hlam, p4950_0]
                            · linarith only [h3, h4941, hlam]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h0, hlam, p4912_0]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [hlam, p4912_0]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h4, hlam, p4912_0]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h3397, hlam, p4912_1]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h3738, hlam, p4912_0]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h1, hlam, p4912_1]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h3969, h4904, hc02, hc24, hlam, hphi, p4912_1]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [hlam, p4912_0]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h3969, hlam, p4912_1]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h4619, hlam, p4912_1]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h2, hlam, p4912_0]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h0, h3397, h4906, hc12, hc45, hlam, hphi, ht23, ht34, p4912_1]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h3397, h4906, hc03, hc45, hlam, hphi, ht34, p4912_1]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [hlam, p4912_0]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h4723, hlam, p4912_0]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h3, hlam, p4912_0]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4912_1]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h1, h4619, h4892, hc12, hc35, hlam, hphi, ht23, p4912_1]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [h4723, hc04, hc45, hlam, hphi, p4912_1]
                          · have p4912_0 := h4912c.1
                            have p4912_1 := h4912c.2.1
                            have p4912_2 := h4912c.2.2.1
                            have p4912_3 := h4912c.2.2.2
                            linarith only [hlam, p4912_0]
                    · linarith only [h1, h3969, h4892, h4904, h4905, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4998 | h4998
                    · linarith only [h1, h4619, h4892, h4904, h4998, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5000 | h5000
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5001 | h5001
                        · rcases h0bigk with h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c | h5002c
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [hlam, p5002_0]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            rcases p5002_3 (m.d 0 1) (by simp) with h5004 | h5004
                            · rcases p5002_3 (m.d 0 2) (by simp) with h5005 | h5005
                              · linarith only [h0, h5005, hlam]
                              · rcases p5002_3 (m.d 0 3) (by simp) with h5007 | h5007
                                · linarith only [h1, h5007, hlam]
                                · linarith only [h4, h5007, hlam]
                            · linarith only [h0, h5004, hlam]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            rcases p5002_3 (m.d 0 1) (by simp) with h5011 | h5011
                            · rcases p5002_3 (m.d 0 2) (by simp) with h5012 | h5012
                              · linarith only [h0, h5012, hlam]
                              · rcases p5002_3 (m.d 0 3) (by simp) with h5014 | h5014
                                · linarith only [h1, h5014, hlam]
                                · rcases p5002_3 (m.d 0 4) (by simp) with h5016 | h5016
                                  · linarith only [h2, h5016, hlam]
                                  · linarith only [h3969, h5016, hlam]
                            · linarith only [h1, h5011, hlam]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            rcases p5002_3 (m.d 0 1) (by simp) with h5020 | h5020
                            · rcases p5002_3 (m.d 0 2) (by simp) with h5021 | h5021
                              · linarith only [h0, h5021, hlam]
                              · rcases p5002_3 (m.d 0 3) (by simp) with h5023 | h5023
                                · linarith only [h1, h5023, hlam]
                                · rcases p5002_3 (m.d 0 4) (by simp) with h5025 | h5025
                                  · linarith only [h2, h5025, hlam]
                                  · rcases p5002_3 (m.d 0 5) (by simp) with h5027 | h5027
                                    · linarith only [h3, h5027, hlam]
                                    · linarith only [h4723, h5027, hlam]
                            · linarith only [h2, h5020, hlam]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            rcases p5002_3 (m.d 0 1) (by simp) with h5031 | h5031
                            · rcases p5002_3 (m.d 0 2) (by simp) with h5032 | h5032
                              · linarith only [h0, h5032, hlam]
                              · rcases p5002_3 (m.d 0 3) (by simp) with h5034 | h5034
                                · linarith only [h1, h5034, hlam]
                                · rcases p5002_3 (m.d 0 4) (by simp) with h5036 | h5036
                                  · linarith only [h2, h5036, hlam]
                                  · rcases p5002_3 (m.d 0 5) (by simp) with h5038 | h5038
                                    · linarith only [h3, h5038, hlam]
                                    · rcases h1bigk with h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c | h5040c
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h0, h3738, hlam, p5002_1, p5040_2]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h1, h4619, hlam, p5002_1, p5040_2]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h2, h4723, hlam, p5002_1, p5040_2]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h3, hlam, p5002_1, p5040_2]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h0, hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h4892, hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h4894, hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h4896, hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h1, hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h1, h3969, h4723, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5002_1, p5040_1]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h4898, hlam, p5040_1]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h4900, hlam, p5040_1]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h2, hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h2, h4723, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5002_1, p5040_1]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h2, h4723, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5002_1, p5040_1]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h4902, hlam, p5040_1]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h3, hlam, p5040_0]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5002_1, p5040_1]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h3, h4892, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5002_1, p5040_1]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p5002_1, p5040_1]
                                      · have p5040_0 := h5040c.1
                                        have p5040_1 := h5040c.2.1
                                        have p5040_2 := h5040c.2.2.1
                                        have p5040_3 := h5040c.2.2.2
                                        linarith only [hlam, p5040_0]
                            · linarith only [h3, h5031, hlam]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h0, hlam, p5002_0]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [hlam, p5002_0]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h4, hlam, p5002_0]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h3397, hlam, p5002_1]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h3738, hlam, p5002_0]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h1, hlam, p5002_1]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h0, h4, h4998, h5001, hc12, hc34, hlam, hphi, ht23, p5002_1]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [hlam, p5002_0]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h3969, hlam, p5002_1]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h4619, hlam, p5002_1]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h2, hlam, p5002_0]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h0, h3397, h4904, hc12, hc34, hlam, hphi, ht23, p5002_1]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h3397, h4904, hc03, hc34, hlam, hphi, p5002_1]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [hlam, p5002_0]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h4723, hlam, p5002_0]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h3, hlam, p5002_0]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h0, h3738, h4904, h5000, hc12, hc34, hlam, hphi, ht23, p5002_1]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h1, h3738, h4892, h4904, h5000, hc12, hc34, hlam, hphi, ht23, p5002_1]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [h4723, h4904, h5000, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5002_1]
                          · have p5002_0 := h5002c.1
                            have p5002_1 := h5002c.2.1
                            have p5002_2 := h5002c.2.2.1
                            have p5002_3 := h5002c.2.2.2
                            linarith only [hlam, p5002_0]
                        · linarith only [h4904, h5000, h5001, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5088 | h5088
                        · linarith only [h0, h4, h4904, h5000, h5088, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h4, h4904, h5088, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 10174000 in
set_option maxHeartbeats 10174000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3397 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3738 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h3969 | h3969
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h3397 h3738 h3969
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h3397 h3738 h3969

set_option maxHeartbeats 10174000 in
set_option maxHeartbeats 10174000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3397 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h3738 | h3738
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h3397 h3738
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h3397 h3738

set_option maxHeartbeats 10174000 in
set_option maxHeartbeats 10174000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h3397 | h3397
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h3397
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h3397

set_option maxHeartbeats 10174000 in
set_option maxHeartbeats 10174000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 10422000 in
set_option maxHeartbeats 10422000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s2 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3 m hb0 hb1 hb3 hb4 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h5091 | h5091
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5092 | h5092
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5093 | h5093
        · linarith only [h0, h3, h5093, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5095 | h5095
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5096 | h5096
            · linarith only [h1, h3, h5096, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5098 | h5098
              · linarith only [h2, h3, h5098, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5100 | h5100
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5101 | h5101
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5102 | h5102
                    · linarith only [h0, h5093, h5102, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5104 | h5104
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5105 | h5105
                        · linarith only [h0, h3, h5096, h5100, h5102, h5105, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h3, h5100, h5105, hc23, hc35, hlam, hphi]
                      · linarith only [h5095, h5096, h5104, hc13, hc35, hlam, hphi]
                  · linarith only [h5092, h5093, h5101, hc12, hc25, hlam, hphi]
                · linarith only [h5091, h5093, h5100, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5111 | h5111
            · linarith only [h0, h3, h5092, h5095, h5111, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5113 | h5113
              · linarith only [h0, h3, h5092, h5113, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5115 | h5115
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5116 | h5116
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5117 | h5117
                    · linarith only [h0, h5093, h5117, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5119 | h5119
                      · linarith only [h1, h3, h5095, h5117, h5119, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5121 | h5121
                        · linarith only [h1, h5111, h5121, hlam]
                        · linarith only [h0, h3, h5115, h5121, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h3, h5092, h5115, h5116, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h5091, h5093, h5115, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5126 | h5126
        · linarith only [h2, h3, h5092, h5126, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5128 | h5128
          · linarith only [h5091, h5092, h5128, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5130 | h5130
            · linarith only [h2, h3, h5091, h5092, h5130, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5132 | h5132
              · linarith only [h2, h3, h5132, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5134 | h5134
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5135 | h5135
                  · linarith only [h0, h5092, h5135, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5137 | h5137
                    · linarith only [h0, h5126, h5137, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5139 | h5139
                      · linarith only [h0, h3, h5128, h5134, h5137, h5139, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5141 | h5141
                        · linarith only [h1, h5130, h5141, hlam]
                        · linarith only [h2, h3, h5134, h5135, h5141, hc23, hc35, hlam, hphi]
                · linarith only [h5091, h5092, h5132, h5134, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5145 | h5145
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5146 | h5146
        · linarith only [h0, h3, h5146, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5148 | h5148
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5149 | h5149
            · linarith only [h1, h3, h5149, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5151 | h5151
              · linarith only [h0, h3, h5145, h5151, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5153 | h5153
                · linarith only [h0, h5091, h5153, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5155 | h5155
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5156 | h5156
                    · linarith only [h0, h5146, h5156, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5158 | h5158
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5159 | h5159
                        · linarith only [h1, h5149, h5159, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5161 | h5161
                          · linarith only [h0, h2, h3, h5091, h5145, h5151, h5161, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h3, h5153, h5155, h5161, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h3, h5148, h5153, h5155, h5158, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h5091, h5145, h5149, h5155, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h5091, h5145, h5148, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5167 | h5167
        · linarith only [h0, h3, h5167, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5169 | h5169
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5170 | h5170
            · linarith only [h1, h3, h5170, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5172 | h5172
              · linarith only [h1, h3, h5169, h5172, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5174 | h5174
                · linarith only [h0, h5091, h5174, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5176 | h5176
                  · linarith only [h0, h3, h5145, h5176, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5178 | h5178
                    · linarith only [h0, h5167, h5178, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5180 | h5180
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5181 | h5181
                        · linarith only [h0, h1, h3, h5145, h5169, h5170, h5178, h5181, hc12, hc25, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5183 | h5183
                          · linarith only [h2, h3, h5172, h5183, hlam]
                          · linarith only [h1, h3, h5180, h5183, hc34, hc45, hlam, hphi]
                      · linarith only [h5169, h5170, h5180, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5187 | h5187
            · linarith only [h1, h3, h5187, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5189 | h5189
              · linarith only [h2, h3, h5189, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5191 | h5191
                · linarith only [h0, h5091, h5191, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5193 | h5193
                  · linarith only [h0, h5145, h5193, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5195 | h5195
                    · linarith only [h0, h5167, h5195, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5197 | h5197
                      · linarith only [h1, h3, h5091, h5169, h5195, h5197, hc02, hc25, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5199 | h5199
                        · linarith only [h1, h3, h5187, h5199, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5201 | h5201
                          · linarith only [h2, h5189, h5201, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5203 | h5203
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5204 | h5204
                              · linarith only [h0, h3, h5199, h5204, hc12, hc23, hlam, hphi]
                              · linarith only [h1, h5169, h5191, h5203, h5204, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5207 | h5207
                              · linarith only [h1, h5187, h5191, h5203, h5207, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5209 | h5209
                                · linarith only [h2, h3, h5191, h5197, h5201, h5209, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5211 | h5211
                                  · linarith only [h0, h5091, h5203, h5209, h5211, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h5091, h5203, h5211, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
