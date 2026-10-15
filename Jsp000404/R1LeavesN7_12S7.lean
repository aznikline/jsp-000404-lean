import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3686 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4101 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4172 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4173 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h4669 | h4669
  · linarith only [h0, h4, h4669, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4671 | h4671
    · linarith only [h0, h3686, h4671, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4673 | h4673
      · linarith only [h0, h4101, h4673, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4675 | h4675
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4676 | h4676
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4677 | h4677
            · linarith only [h2, h4173, h4677, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4679 | h4679
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4680 | h4680
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4681 | h4681
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4682 | h4682
                    · linarith only [h3686, h4, h4172, h4173, h4682, hc02, hc23, hlam, hphi]
                    · rcases h1bigk with h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c | h4684c
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        rcases p4684_3 (m.d 0 1) (by simp) with h4686 | h4686
                        · rcases p4684_3 (m.d 1 2) (by simp) with h4687 | h4687
                          · linarith only [h4687, hlam, p4684_0]
                          · rcases p4684_3 (m.d 1 3) (by simp) with h4689 | h4689
                            · linarith only [h1, h4689, hlam]
                            · linarith only [h4669, h4689, hlam]
                        · linarith only [h4686, hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h4676, hc01, hlam, hphi, ht0b, ht5b, p4684_1, u5ehi3]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        rcases p4684_3 (m.d 0 1) (by simp) with h4694 | h4694
                        · rcases p4684_3 (m.d 1 2) (by simp) with h4695 | h4695
                          · linarith only [h0, h4695, hlam]
                          · rcases p4684_3 (m.d 1 3) (by simp) with h4697 | h4697
                            · linarith only [h1, h4697, hlam]
                            · linarith only [h4675, h4697, hlam]
                        · linarith only [h4694, hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        rcases p4684_3 (m.d 0 1) (by simp) with h4701 | h4701
                        · rcases p4684_3 (m.d 1 2) (by simp) with h4702 | h4702
                          · linarith only [h0, h4702, hlam]
                          · rcases p4684_3 (m.d 1 3) (by simp) with h4704 | h4704
                            · linarith only [h1, h4704, hlam]
                            · linarith only [h4676, h4704, hlam]
                        · linarith only [h4701, hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h0, hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h4669, hlam, p4684_1]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h4671, hlam, p4684_1]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h4673, hlam, p4684_1]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h1, hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        rcases p4684_3 (m.d 0 1) (by simp) with h4714 | h4714
                        · rcases p4684_3 (m.d 1 2) (by simp) with h4715 | h4715
                          · linarith only [h4669, h4715, hlam]
                          · rcases p4684_3 (m.d 1 3) (by simp) with h4717 | h4717
                            · rcases p4684_3 (m.d 1 4) (by simp) with h4718 | h4718
                              · linarith only [h4675, h4718, hlam]
                              · linarith only [h4671, h4718, hlam]
                            · linarith only [h4669, h4717, hlam]
                        · linarith only [h0, h4714, hlam]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        rcases p4684_3 (m.d 0 1) (by simp) with h4724 | h4724
                        · rcases p4684_3 (m.d 1 2) (by simp) with h4725 | h4725
                          · linarith only [h4669, h4725, hlam]
                          · rcases p4684_3 (m.d 1 3) (by simp) with h4727 | h4727
                            · rcases p4684_3 (m.d 1 4) (by simp) with h4728 | h4728
                              · linarith only [h4675, h4728, hlam]
                              · rcases p4684_3 (m.d 1 5) (by simp) with h4730 | h4730
                                · linarith only [h4676, h4730, hlam]
                                · linarith only [h4677, h4730, hlam]
                            · linarith only [h4675, h4727, hlam]
                        · linarith only [h2, h4724, hlam]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p4684_1, u5ehi1]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h2, hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h2, h4173, h4681, hc12, hc24, hlam, hphi, p4684_1]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h4675, hlam, p4684_1]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h4677, hlam, p4684_1]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h3, hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h3, h4173, h4681, hc12, hc24, hlam, hphi, p4684_1]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h4676, hlam, p4684_0]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [h3, h4173, h4671, h4681, hc12, hc24, hlam, hphi, p4684_1]
                      · have p4684_0 := h4684c.1
                        have p4684_1 := h4684c.2.1
                        have p4684_2 := h4684c.2.2.1
                        have p4684_3 := h4684c.2.2.2
                        linarith only [hlam, p4684_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4746 | h4746
                    · linarith only [h3686, h4681, h4746, hc02, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c | h4748c
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        rcases p4748_3 (m.d 0 1) (by simp) with h4750 | h4750
                        · rcases p4748_3 (m.d 1 2) (by simp) with h4751 | h4751
                          · linarith only [h4751, hlam, p4748_0]
                          · rcases p4748_3 (m.d 1 3) (by simp) with h4753 | h4753
                            · linarith only [h1, h4753, hlam]
                            · linarith only [h4669, h4753, hlam]
                        · linarith only [h4750, hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h4676, hc01, hlam, hphi, ht0b, ht5b, p4748_1, u5ehi3]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        rcases p4748_3 (m.d 0 1) (by simp) with h4758 | h4758
                        · rcases p4748_3 (m.d 1 2) (by simp) with h4759 | h4759
                          · linarith only [h0, h4759, hlam]
                          · rcases p4748_3 (m.d 1 3) (by simp) with h4761 | h4761
                            · linarith only [h1, h4761, hlam]
                            · linarith only [h4675, h4761, hlam]
                        · linarith only [h4758, hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        rcases p4748_3 (m.d 0 1) (by simp) with h4765 | h4765
                        · rcases p4748_3 (m.d 1 2) (by simp) with h4766 | h4766
                          · linarith only [h0, h4766, hlam]
                          · rcases p4748_3 (m.d 1 3) (by simp) with h4768 | h4768
                            · linarith only [h1, h4768, hlam]
                            · linarith only [h4676, h4768, hlam]
                        · linarith only [h4765, hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h0, hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h4669, hlam, p4748_1]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h4671, hlam, p4748_1]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h4673, hlam, p4748_1]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h1, hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        rcases p4748_3 (m.d 0 1) (by simp) with h4778 | h4778
                        · rcases p4748_3 (m.d 1 2) (by simp) with h4779 | h4779
                          · linarith only [h4669, h4779, hlam]
                          · rcases p4748_3 (m.d 1 3) (by simp) with h4781 | h4781
                            · rcases p4748_3 (m.d 1 4) (by simp) with h4782 | h4782
                              · linarith only [h4675, h4782, hlam]
                              · linarith only [h4671, h4782, hlam]
                            · linarith only [h4669, h4781, hlam]
                        · linarith only [h0, h4778, hlam]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        rcases p4748_3 (m.d 0 1) (by simp) with h4788 | h4788
                        · rcases p4748_3 (m.d 1 2) (by simp) with h4789 | h4789
                          · linarith only [h4669, h4789, hlam]
                          · rcases p4748_3 (m.d 1 3) (by simp) with h4791 | h4791
                            · rcases p4748_3 (m.d 1 4) (by simp) with h4792 | h4792
                              · linarith only [h4675, h4792, hlam]
                              · rcases p4748_3 (m.d 1 5) (by simp) with h4794 | h4794
                                · linarith only [h4676, h4794, hlam]
                                · linarith only [h4677, h4794, hlam]
                            · linarith only [h4675, h4791, hlam]
                        · linarith only [h2, h4788, hlam]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p4748_1, u5ehi1]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h2, hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h2, h3686, h4681, hc12, hc45, hlam, hphi, ht23, ht34, p4748_1]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h4675, hlam, p4748_1]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h4677, hlam, p4748_1]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h3, hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        rcases p4748_3 (m.d 0 1) (by simp) with h4806 | h4806
                        · rcases p4748_3 (m.d 1 2) (by simp) with h4807 | h4807
                          · linarith only [h4673, h4807, hlam]
                          · rcases p4748_3 (m.d 1 3) (by simp) with h4809 | h4809
                            · rcases p4748_3 (m.d 1 4) (by simp) with h4810 | h4810
                              · linarith only [h4677, h4810, hlam]
                              · linarith only [h4671, h4810, hlam]
                            · linarith only [h4669, h4809, hlam]
                        · linarith only [h0, h4806, hlam]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [h4676, hlam, p4748_0]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        rcases p4748_3 (m.d 0 1) (by simp) with h4816 | h4816
                        · rcases p4748_3 (m.d 1 2) (by simp) with h4817 | h4817
                          · linarith only [h4673, h4817, hlam]
                          · rcases p4748_3 (m.d 1 3) (by simp) with h4819 | h4819
                            · rcases p4748_3 (m.d 1 4) (by simp) with h4820 | h4820
                              · linarith only [h4677, h4820, hlam]
                              · rcases p4748_3 (m.d 1 5) (by simp) with h4822 | h4822
                                · rcases h2bigk with h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p4823_1]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h4, hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h3686, hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h4101, hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h0, hlam, p4823_1]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h4669, hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h4671, hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h4673, hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    rcases p4823_3 (m.d 0 2) (by simp) with h4834 | h4834
                                    · linarith only [h4834, hlam, p4823_0]
                                    · rcases p4823_3 (m.d 1 2) (by simp) with h4836 | h4836
                                      · linarith only [h4669, h4836, hlam]
                                      · rcases p4823_3 (m.d 2 3) (by simp) with h4838 | h4838
                                        · rcases p4823_3 (m.d 2 4) (by simp) with h4839 | h4839
                                          · linarith only [h4679, h4839, hlam]
                                          · linarith only [h3686, h4839, hlam]
                                        · linarith only [h4838, hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    rcases p4823_3 (m.d 0 2) (by simp) with h4843 | h4843
                                    · linarith only [h4, h4843, hlam]
                                    · linarith only [h0, h4843, hlam]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h3686, hc02, hc23, hlam, hphi, p4823_1]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h3, h4101, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4748_1, p4823_1]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h0, h4681, hc12, hc45, hlam, hphi, ht23, ht34, p4823_1]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h4681, hc12, hc45, hlam, hphi, ht23, ht34, p4823_1]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h4679, hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h4681, hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    rcases p4823_3 (m.d 0 2) (by simp) with h4854 | h4854
                                    · linarith only [h4854, hlam, p4823_0]
                                    · rcases p4823_3 (m.d 1 2) (by simp) with h4856 | h4856
                                      · linarith only [h4673, h4856, hlam]
                                      · rcases p4823_3 (m.d 2 3) (by simp) with h4858 | h4858
                                        · rcases p4823_3 (m.d 2 4) (by simp) with h4859 | h4859
                                          · linarith only [h4681, h4859, hlam]
                                          · linarith only [h3686, h4859, hlam]
                                        · linarith only [h4, h4858, hlam]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    rcases p4823_3 (m.d 0 2) (by simp) with h4863 | h4863
                                    · linarith only [h4101, h4863, hlam]
                                    · linarith only [h0, h4863, hlam]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h4680, hlam, p4823_0]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [h0, h3686, hc12, hc25, hlam, hphi, p4823_1]
                                  · have p4823_0 := h4823c.1
                                    have p4823_1 := h4823c.2.1
                                    have p4823_2 := h4823c.2.2.1
                                    have p4823_3 := h4823c.2.2.2
                                    linarith only [hlam, p4823_0]
                                · linarith only [h4677, h4822, hlam]
                            · linarith only [h4675, h4819, hlam]
                        · linarith only [h2, h4816, hlam]
                      · have p4748_0 := h4748c.1
                        have p4748_1 := h4748c.2.1
                        have p4748_2 := h4748c.2.2.1
                        have p4748_3 := h4748c.2.2.2
                        linarith only [hlam, p4748_0]
                · linarith only [h1, h4, h4676, h4680, hlam]
              · linarith only [h4, h4172, h4679, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4875 | h4875
            · linarith only [h2, h4173, h4875, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4877 | h4877
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4878 | h4878
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4879 | h4879
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4880 | h4880
                    · linarith only [h0, h3, h3686, h4173, h4675, h4676, h4880, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c | h4882c
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        rcases p4882_3 (m.d 0 1) (by simp) with h4884 | h4884
                        · rcases p4882_3 (m.d 1 2) (by simp) with h4885 | h4885
                          · linarith only [h4885, hlam, p4882_0]
                          · rcases p4882_3 (m.d 1 3) (by simp) with h4887 | h4887
                            · linarith only [h1, h4887, hlam]
                            · linarith only [h4669, h4887, hlam]
                        · linarith only [h4884, hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        rcases p4882_3 (m.d 0 1) (by simp) with h4891 | h4891
                        · rcases p4882_3 (m.d 1 2) (by simp) with h4892 | h4892
                          · linarith only [h0, h4892, hlam]
                          · rcases p4882_3 (m.d 1 3) (by simp) with h4894 | h4894
                            · linarith only [h4894, hlam, p4882_0]
                            · rcases p4882_3 (m.d 1 4) (by simp) with h4896 | h4896
                              · linarith only [h2, h4896, hlam]
                              · rcases p4882_3 (m.d 1 5) (by simp) with h4898 | h4898
                                · linarith only [h3, h4898, hlam]
                                · linarith only [h4676, h4898, hlam]
                        · linarith only [h4891, hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        rcases p4882_3 (m.d 0 1) (by simp) with h4902 | h4902
                        · rcases p4882_3 (m.d 1 2) (by simp) with h4903 | h4903
                          · linarith only [h0, h4903, hlam]
                          · rcases p4882_3 (m.d 1 3) (by simp) with h4905 | h4905
                            · linarith only [h1, h4905, hlam]
                            · linarith only [h4675, h4905, hlam]
                        · linarith only [h4902, hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        rcases p4882_3 (m.d 0 1) (by simp) with h4909 | h4909
                        · rcases p4882_3 (m.d 1 2) (by simp) with h4910 | h4910
                          · linarith only [h0, h4910, hlam]
                          · rcases p4882_3 (m.d 1 3) (by simp) with h4912 | h4912
                            · linarith only [h1, h4912, hlam]
                            · rcases p4882_3 (m.d 1 4) (by simp) with h4914 | h4914
                              · linarith only [h2, h4914, hlam]
                              · rcases p4882_3 (m.d 1 5) (by simp) with h4916 | h4916
                                · linarith only [h4916, hlam, p4882_0]
                                · rcases h2bigk with h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h3686, h4173, h4879, hc12, hc24, hlam, hphi, p4918_1]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4, hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h3686, hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4101, hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h0, hlam, p4918_1]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4669, hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4671, hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4673, hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    rcases p4918_3 (m.d 0 2) (by simp) with h4929 | h4929
                                    · linarith only [h4929, hlam, p4918_0]
                                    · rcases p4918_3 (m.d 1 2) (by simp) with h4931 | h4931
                                      · linarith only [h4669, h4931, hlam]
                                      · rcases p4918_3 (m.d 2 3) (by simp) with h4933 | h4933
                                        · rcases p4918_3 (m.d 2 4) (by simp) with h4934 | h4934
                                          · linarith only [h4877, h4934, hlam]
                                          · linarith only [h3686, h4934, hlam]
                                        · linarith only [h4933, hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    rcases p4918_3 (m.d 0 2) (by simp) with h4938 | h4938
                                    · linarith only [h4, h4938, hlam]
                                    · linarith only [h0, h4938, hlam]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4675, h4676, h4879, h4880, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4918_1]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4101, hc02, hc23, hlam, hphi, p4918_1]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    rcases p4918_3 (m.d 0 2) (by simp) with h4944 | h4944
                                    · linarith only [h4944, hlam, p4918_0]
                                    · rcases p4918_3 (m.d 1 2) (by simp) with h4946 | h4946
                                      · linarith only [h4671, h4946, hlam]
                                      · rcases p4918_3 (m.d 2 3) (by simp) with h4948 | h4948
                                        · rcases p4918_3 (m.d 2 4) (by simp) with h4949 | h4949
                                          · rcases p4918_3 (m.d 2 5) (by simp) with h4950 | h4950
                                            · linarith only [h4879, h4950, hlam]
                                            · linarith only [h4101, h4950, hlam]
                                          · linarith only [h4949, hlam, p4918_0]
                                        · linarith only [h4, h4948, hlam]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    rcases p4918_3 (m.d 0 2) (by simp) with h4955 | h4955
                                    · linarith only [h3686, h4955, hlam]
                                    · linarith only [h0, h4955, hlam]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4877, hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4675, h4676, h4879, h4880, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4918_1]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    rcases p4918_3 (m.d 0 2) (by simp) with h4961 | h4961
                                    · linarith only [h4961, hlam, p4918_0]
                                    · rcases p4918_3 (m.d 1 2) (by simp) with h4963 | h4963
                                      · linarith only [h4673, h4963, hlam]
                                      · rcases p4918_3 (m.d 2 3) (by simp) with h4965 | h4965
                                        · rcases p4918_3 (m.d 2 4) (by simp) with h4966 | h4966
                                          · rcases p4918_3 (m.d 2 5) (by simp) with h4967 | h4967
                                            · rcases h4bigk with h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c | h4968c
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4173, hc14, hc45, hlam, hphi, p4968_1]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h3686, hlam, p4968_1]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4173, hc34, hc45, hlam, hphi, p4968_1]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4173, hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h2, hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4671, hlam, p4968_1]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h2, h4173, hc34, hc45, hlam, hphi, p4968_1]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4875, hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                rcases p4968_3 (m.d 0 4) (by simp) with h4979 | h4979
                                                · linarith only [h3686, h4979, hlam]
                                                · rcases p4968_3 (m.d 1 4) (by simp) with h4981 | h4981
                                                  · linarith only [h4671, h4981, hlam]
                                                  · rcases p4968_3 (m.d 2 4) (by simp) with h4983 | h4983
                                                    · rcases p4968_3 (m.d 3 4) (by simp) with h4984 | h4984
                                                      · linarith only [h4877, h4984, hlam]
                                                      · rcases p4968_3 (m.d 4 5) (by simp) with h4986 | h4986
                                                        · linarith only [h4879, h4986, hlam]
                                                        · linarith only [h4173, h4986, hlam]
                                                    · linarith only [h3686, h4983, hlam]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                rcases p4968_3 (m.d 0 4) (by simp) with h4990 | h4990
                                                · linarith only [h3686, h4990, hlam]
                                                · linarith only [h2, h4990, hlam]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4675, h4676, h4879, h4880, hlam, p4968_2]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h0, h3686, h4173, hc12, hc24, hlam, hphi, p4968_1]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4172, hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4675, hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4877, hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4880, hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h0, h3686, h4877, h4879, hc12, hc23, hlam, hphi, p4968_1]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4671, h4877, h4879, hc12, hc23, hlam, hphi, p4968_1]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [h4879, hlam, p4968_0]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                rcases p4968_3 (m.d 0 4) (by simp) with h5004 | h5004
                                                · linarith only [h4173, h5004, hlam]
                                                · linarith only [h4172, h5004, hlam]
                                              · have p4968_0 := h4968c.1
                                                have p4968_1 := h4968c.2.1
                                                have p4968_2 := h4968c.2.2.1
                                                have p4968_3 := h4968c.2.2.2
                                                linarith only [hlam, p4968_0]
                                            · linarith only [h4967, hlam, p4918_0]
                                          · linarith only [h3686, h4966, hlam]
                                        · linarith only [h4, h4965, hlam]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    rcases p4918_3 (m.d 0 2) (by simp) with h5011 | h5011
                                    · linarith only [h4101, h5011, hlam]
                                    · linarith only [h0, h5011, hlam]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4878, hlam, p4918_0]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [h4879, hlam, p4918_1]
                                  · have p4918_0 := h4918c.1
                                    have p4918_1 := h4918c.2.1
                                    have p4918_2 := h4918c.2.2.1
                                    have p4918_3 := h4918c.2.2.2
                                    linarith only [hlam, p4918_0]
                        · linarith only [h4909, hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h0, hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h4669, hlam, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h4671, hlam, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h4673, hlam, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h1, hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h4676, h4877, h4879, h4880, hc12, hc23, hlam, hphi, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h4671, h4676, h4877, h4879, h4880, hc12, hc23, hlam, hphi, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h4676, hlam, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h2, hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h2, h4173, h4877, h4879, hc12, hc23, hlam, hphi, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h4675, hlam, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h4875, hlam, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h3, hlam, p4882_0]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h3, h4173, h4877, h4879, hc12, hc23, hlam, hphi, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h3, h4173, h4675, h4877, h4879, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [h3, h4173, h4671, h4877, h4879, hc12, hc23, hlam, hphi, p4882_1]
                      · have p4882_0 := h4882c.1
                        have p4882_1 := h4882c.2.1
                        have p4882_2 := h4882c.2.2.1
                        have p4882_3 := h4882c.2.2.2
                        linarith only [hlam, p4882_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5038 | h5038
                    · linarith only [h0, h3686, h4675, h4879, h5038, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
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
                        rcases p5040_3 (m.d 0 1) (by simp) with h5042 | h5042
                        · rcases p5040_3 (m.d 1 2) (by simp) with h5043 | h5043
                          · linarith only [h5043, hlam, p5040_0]
                          · rcases p5040_3 (m.d 1 3) (by simp) with h5045 | h5045
                            · linarith only [h1, h5045, hlam]
                            · linarith only [h4669, h5045, hlam]
                        · linarith only [h5042, hlam, p5040_0]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        rcases p5040_3 (m.d 0 1) (by simp) with h5049 | h5049
                        · rcases p5040_3 (m.d 1 2) (by simp) with h5050 | h5050
                          · linarith only [h0, h5050, hlam]
                          · rcases p5040_3 (m.d 1 3) (by simp) with h5052 | h5052
                            · linarith only [h5052, hlam, p5040_0]
                            · rcases p5040_3 (m.d 1 4) (by simp) with h5054 | h5054
                              · linarith only [h2, h5054, hlam]
                              · rcases p5040_3 (m.d 1 5) (by simp) with h5056 | h5056
                                · linarith only [h3, h5056, hlam]
                                · linarith only [h4676, h5056, hlam]
                        · linarith only [h5049, hlam, p5040_0]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        rcases p5040_3 (m.d 0 1) (by simp) with h5060 | h5060
                        · rcases p5040_3 (m.d 1 2) (by simp) with h5061 | h5061
                          · linarith only [h0, h5061, hlam]
                          · rcases p5040_3 (m.d 1 3) (by simp) with h5063 | h5063
                            · linarith only [h1, h5063, hlam]
                            · linarith only [h4675, h5063, hlam]
                        · linarith only [h5060, hlam, p5040_0]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        rcases p5040_3 (m.d 0 1) (by simp) with h5067 | h5067
                        · rcases p5040_3 (m.d 1 2) (by simp) with h5068 | h5068
                          · linarith only [h0, h5068, hlam]
                          · rcases p5040_3 (m.d 1 3) (by simp) with h5070 | h5070
                            · linarith only [h1, h5070, hlam]
                            · rcases p5040_3 (m.d 1 4) (by simp) with h5072 | h5072
                              · linarith only [h2, h5072, hlam]
                              · rcases p5040_3 (m.d 1 5) (by simp) with h5074 | h5074
                                · linarith only [h5074, hlam, p5040_0]
                                · rcases h2bigk with h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c | h5076c
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h3686, hc12, hc24, hlam, hphi, p5076_1]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h4, hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h3686, hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h4101, hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h0, hlam, p5076_1]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h4669, hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h4671, hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h4673, hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    rcases p5076_3 (m.d 0 2) (by simp) with h5087 | h5087
                                    · linarith only [h5087, hlam, p5076_0]
                                    · rcases p5076_3 (m.d 1 2) (by simp) with h5089 | h5089
                                      · linarith only [h4669, h5089, hlam]
                                      · rcases p5076_3 (m.d 2 3) (by simp) with h5091 | h5091
                                        · rcases p5076_3 (m.d 2 4) (by simp) with h5092 | h5092
                                          · linarith only [h4877, h5092, hlam]
                                          · linarith only [h3686, h5092, hlam]
                                        · linarith only [h5091, hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    rcases p5076_3 (m.d 0 2) (by simp) with h5096 | h5096
                                    · linarith only [h4, h5096, hlam]
                                    · linarith only [h0, h5096, hlam]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h3686, hc02, hc23, hlam, hphi, p5076_1]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h4675, h4676, h4878, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5076_1]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h0, h4879, hc12, hc45, hlam, hphi, ht23, ht34, p5076_1]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h4879, hc12, hc45, hlam, hphi, ht23, ht34, p5076_1]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h4877, hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h4879, hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    rcases p5076_3 (m.d 0 2) (by simp) with h5107 | h5107
                                    · linarith only [h5107, hlam, p5076_0]
                                    · rcases p5076_3 (m.d 1 2) (by simp) with h5109 | h5109
                                      · linarith only [h4673, h5109, hlam]
                                      · rcases p5076_3 (m.d 2 3) (by simp) with h5111 | h5111
                                        · rcases p5076_3 (m.d 2 4) (by simp) with h5112 | h5112
                                          · linarith only [h4879, h5112, hlam]
                                          · linarith only [h3686, h5112, hlam]
                                        · linarith only [h4, h5111, hlam]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    rcases p5076_3 (m.d 0 2) (by simp) with h5116 | h5116
                                    · linarith only [h4101, h5116, hlam]
                                    · linarith only [h0, h5116, hlam]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h4878, hlam, p5076_0]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [h0, h3686, hc12, hc25, hlam, hphi, p5076_1]
                                  · have p5076_0 := h5076c.1
                                    have p5076_1 := h5076c.2.1
                                    have p5076_2 := h5076c.2.2.1
                                    have p5076_3 := h5076c.2.2.2
                                    linarith only [hlam, p5076_0]
                        · linarith only [h5067, hlam, p5040_0]
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
                        linarith only [h4669, hlam, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h4671, hlam, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h4673, hlam, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h1, hlam, p5040_0]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h4676, hc12, hc35, hlam, hphi, ht23, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [hlam, p5040_0]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h4671, h4676, hc12, hc35, hlam, hphi, ht23, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h4676, hlam, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h2, hlam, p5040_0]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h2, h4173, hc12, hc45, hlam, hphi, ht23, ht34, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h4675, hlam, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [hlam, p5040_0]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h4875, hlam, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h3, hlam, p5040_0]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h4676, h4878, hc12, hc23, hlam, hphi, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h4669, h4676, h4878, hc12, hc23, hlam, hphi, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [h4671, h4676, h4878, hc12, hc23, hlam, hphi, p5040_1]
                      · have p5040_0 := h5040c.1
                        have p5040_1 := h5040c.2.1
                        have p5040_2 := h5040c.2.2.1
                        have p5040_3 := h5040c.2.2.2
                        linarith only [hlam, p5040_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5143 | h5143
                  · linarith only [h2, h4173, h4671, h4877, h4878, h5143, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5145 | h5145
                    · linarith only [h0, h2, h3686, h4101, h4675, h4877, h4878, h5143, h5145, hc12, hc35, hlam, hphi, ht23]
                    · rcases h1bigk with h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        rcases p5147_3 (m.d 0 1) (by simp) with h5149 | h5149
                        · rcases p5147_3 (m.d 1 2) (by simp) with h5150 | h5150
                          · linarith only [h5150, hlam, p5147_0]
                          · rcases p5147_3 (m.d 1 3) (by simp) with h5152 | h5152
                            · linarith only [h1, h5152, hlam]
                            · linarith only [h4669, h5152, hlam]
                        · linarith only [h5149, hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        rcases p5147_3 (m.d 0 1) (by simp) with h5156 | h5156
                        · rcases p5147_3 (m.d 1 2) (by simp) with h5157 | h5157
                          · linarith only [h0, h5157, hlam]
                          · rcases p5147_3 (m.d 1 3) (by simp) with h5159 | h5159
                            · linarith only [h5159, hlam, p5147_0]
                            · rcases p5147_3 (m.d 1 4) (by simp) with h5161 | h5161
                              · linarith only [h2, h5161, hlam]
                              · rcases p5147_3 (m.d 1 5) (by simp) with h5163 | h5163
                                · linarith only [h3, h5163, hlam]
                                · linarith only [h4676, h5163, hlam]
                        · linarith only [h5156, hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        rcases p5147_3 (m.d 0 1) (by simp) with h5167 | h5167
                        · rcases p5147_3 (m.d 1 2) (by simp) with h5168 | h5168
                          · linarith only [h0, h5168, hlam]
                          · rcases p5147_3 (m.d 1 3) (by simp) with h5170 | h5170
                            · linarith only [h1, h5170, hlam]
                            · linarith only [h4675, h5170, hlam]
                        · linarith only [h5167, hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        rcases p5147_3 (m.d 0 1) (by simp) with h5174 | h5174
                        · rcases p5147_3 (m.d 1 2) (by simp) with h5175 | h5175
                          · linarith only [h0, h5175, hlam]
                          · rcases p5147_3 (m.d 1 3) (by simp) with h5177 | h5177
                            · linarith only [h1, h5177, hlam]
                            · rcases p5147_3 (m.d 1 4) (by simp) with h5179 | h5179
                              · linarith only [h2, h5179, hlam]
                              · rcases p5147_3 (m.d 1 5) (by simp) with h5181 | h5181
                                · linarith only [h5181, hlam, p5147_0]
                                · rcases h2bigk with h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c | h5183c
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4, h4878, h5145, hc12, hc45, hlam, hphi, ht23, ht34, p5183_1]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4, hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h3686, hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4101, hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h0, hlam, p5183_1]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4669, hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4671, hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4673, hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4878, h5145, hc02, hc45, hlam, hphi, ht23, ht34, p5183_1]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4878, h5145, hc12, hc45, hlam, hphi, ht23, ht34, p5183_1]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h3686, h4878, h5145, hc04, hc45, hlam, hphi, p5183_1]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4878, hlam, p5183_1]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h0, h4877, h4878, h5145, hc12, hc45, hlam, hphi, ht23, ht34, p5183_1]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4877, h4878, h5145, hc12, hc45, hlam, hphi, ht23, ht34, p5183_1]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h4877, hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h5143, hlam, p5183_0]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    rcases p5183_3 (m.d 0 2) (by simp) with h5204 | h5204
                                    · linarith only [h5204, hlam, p5183_0]
                                    · rcases p5183_3 (m.d 1 2) (by simp) with h5206 | h5206
                                      · linarith only [h4673, h5206, hlam]
                                      · rcases p5183_3 (m.d 2 3) (by simp) with h5208 | h5208
                                        · linarith only [h4878, h5208, hlam]
                                        · linarith only [h4, h5208, hlam]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    rcases p5183_3 (m.d 0 2) (by simp) with h5211 | h5211
                                    · linarith only [h4101, h5211, hlam]
                                    · linarith only [h0, h5211, hlam]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h0, h4, hc12, hc25, hlam, hphi, p5183_1]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [h0, h3686, h4878, h5145, hc12, hc45, hlam, hphi, ht23, ht34, p5183_1]
                                  · have p5183_0 := h5183c.1
                                    have p5183_1 := h5183c.2.1
                                    have p5183_2 := h5183c.2.2.1
                                    have p5183_3 := h5183c.2.2.2
                                    linarith only [hlam, p5183_0]
                        · linarith only [h5174, hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h0, hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h4669, hlam, p5147_1]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h4671, hlam, p5147_1]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h4673, hlam, p5147_1]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h1, hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h4676, h5145, hc12, hc45, hlam, hphi, ht23, ht34, p5147_1]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h4671, h4676, h5145, hc12, hc45, hlam, hphi, ht23, ht34, p5147_1]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h4676, hlam, p5147_1]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h2, hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h2, h4173, hc12, hc45, hlam, hphi, ht23, ht34, p5147_1]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h4675, hlam, p5147_1]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h4875, hlam, p5147_1]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h3, hlam, p5147_0]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        rcases p5147_3 (m.d 0 1) (by simp) with h5234 | h5234
                        · rcases p5147_3 (m.d 1 2) (by simp) with h5235 | h5235
                          · linarith only [h4673, h5235, hlam]
                          · rcases p5147_3 (m.d 1 3) (by simp) with h5237 | h5237
                            · linarith only [h4676, h5237, hlam]
                            · linarith only [h4669, h5237, hlam]
                        · linarith only [h0, h5234, hlam]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [h3, h4101, h4675, h4878, h5145, hc34, hc45, hlam, hphi, p5147_1]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        rcases p5147_3 (m.d 0 1) (by simp) with h5242 | h5242
                        · rcases p5147_3 (m.d 1 2) (by simp) with h5243 | h5243
                          · linarith only [h4673, h5243, hlam]
                          · rcases p5147_3 (m.d 1 3) (by simp) with h5245 | h5245
                            · linarith only [h4676, h5245, hlam]
                            · linarith only [h4675, h5245, hlam]
                        · linarith only [h2, h5242, hlam]
                      · have p5147_0 := h5147c.1
                        have p5147_1 := h5147c.2.1
                        have p5147_2 := h5147c.2.2.1
                        have p5147_3 := h5147c.2.2.2
                        linarith only [hlam, p5147_0]
              · linarith only [h1, h4, h4675, h4877, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5251 | h5251
          · linarith only [h4172, h4675, h5251, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5253 | h5253
            · linarith only [h4172, h4173, h4675, h5253, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5255 | h5255
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5256 | h5256
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5257 | h5257
                  · linarith only [h4172, h4173, h4669, h4675, h5257, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5259 | h5259
                    · linarith only [h0, h3686, h4172, h5257, h5259, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c | h5261c
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        rcases p5261_3 (m.d 0 1) (by simp) with h5263 | h5263
                        · rcases p5261_3 (m.d 1 2) (by simp) with h5264 | h5264
                          · linarith only [h5264, hlam, p5261_0]
                          · rcases p5261_3 (m.d 1 3) (by simp) with h5266 | h5266
                            · linarith only [h1, h5266, hlam]
                            · linarith only [h4669, h5266, hlam]
                        · linarith only [h5263, hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        rcases p5261_3 (m.d 0 1) (by simp) with h5270 | h5270
                        · rcases p5261_3 (m.d 1 2) (by simp) with h5271 | h5271
                          · linarith only [h0, h5271, hlam]
                          · rcases p5261_3 (m.d 1 3) (by simp) with h5273 | h5273
                            · linarith only [h5273, hlam, p5261_0]
                            · rcases p5261_3 (m.d 1 4) (by simp) with h5275 | h5275
                              · linarith only [h2, h5275, hlam]
                              · linarith only [h4675, h5275, hlam]
                        · linarith only [h5270, hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        rcases p5261_3 (m.d 0 1) (by simp) with h5279 | h5279
                        · rcases p5261_3 (m.d 1 2) (by simp) with h5280 | h5280
                          · linarith only [h0, h5280, hlam]
                          · rcases p5261_3 (m.d 1 3) (by simp) with h5282 | h5282
                            · linarith only [h1, h5282, hlam]
                            · rcases p5261_3 (m.d 1 4) (by simp) with h5284 | h5284
                              · linarith only [h5284, hlam, p5261_0]
                              · rcases p5261_3 (m.d 1 5) (by simp) with h5286 | h5286
                                · linarith only [h3, h5286, hlam]
                                · linarith only [h5253, h5286, hlam]
                        · linarith only [h5279, hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        rcases p5261_3 (m.d 0 1) (by simp) with h5290 | h5290
                        · rcases p5261_3 (m.d 1 2) (by simp) with h5291 | h5291
                          · linarith only [h0, h5291, hlam]
                          · rcases p5261_3 (m.d 1 3) (by simp) with h5293 | h5293
                            · linarith only [h1, h5293, hlam]
                            · rcases p5261_3 (m.d 1 4) (by simp) with h5295 | h5295
                              · linarith only [h2, h5295, hlam]
                              · rcases p5261_3 (m.d 1 5) (by simp) with h5297 | h5297
                                · linarith only [h5297, hlam, p5261_0]
                                · rcases h2bigk with h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c | h5299c
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p5299_1]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h4, hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h3686, hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h4101, hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h0, hlam, p5299_1]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h4669, hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h4671, hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h4673, hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    rcases p5299_3 (m.d 0 2) (by simp) with h5310 | h5310
                                    · linarith only [h5310, hlam, p5299_0]
                                    · rcases p5299_3 (m.d 1 2) (by simp) with h5312 | h5312
                                      · linarith only [h4669, h5312, hlam]
                                      · rcases p5299_3 (m.d 2 3) (by simp) with h5314 | h5314
                                        · rcases p5299_3 (m.d 2 4) (by simp) with h5315 | h5315
                                          · linarith only [h5255, h5315, hlam]
                                          · linarith only [h3686, h5315, hlam]
                                        · linarith only [h5314, hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    rcases p5299_3 (m.d 0 2) (by simp) with h5319 | h5319
                                    · linarith only [h4, h5319, hlam]
                                    · linarith only [h0, h5319, hlam]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h3686, hc02, hc23, hlam, hphi, p5299_1]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h4101, h4172, h4173, h4669, h4675, hc12, hc23, hlam, hphi, p5299_1]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h0, h5257, hc12, hc45, hlam, hphi, ht23, ht34, p5299_1]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h5257, hc12, hc45, hlam, hphi, ht23, ht34, p5299_1]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h5255, hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h5257, hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    rcases p5299_3 (m.d 0 2) (by simp) with h5330 | h5330
                                    · linarith only [h5330, hlam, p5299_0]
                                    · rcases p5299_3 (m.d 1 2) (by simp) with h5332 | h5332
                                      · linarith only [h4673, h5332, hlam]
                                      · rcases p5299_3 (m.d 2 3) (by simp) with h5334 | h5334
                                        · rcases p5299_3 (m.d 2 4) (by simp) with h5335 | h5335
                                          · linarith only [h5257, h5335, hlam]
                                          · linarith only [h3686, h5335, hlam]
                                        · linarith only [h4, h5334, hlam]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    rcases p5299_3 (m.d 0 2) (by simp) with h5339 | h5339
                                    · linarith only [h4101, h5339, hlam]
                                    · linarith only [h0, h5339, hlam]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h5256, hlam, p5299_0]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [h0, h3686, hc12, hc25, hlam, hphi, p5299_1]
                                  · have p5299_0 := h5299c.1
                                    have p5299_1 := h5299c.2.1
                                    have p5299_2 := h5299c.2.2.1
                                    have p5299_3 := h5299c.2.2.2
                                    linarith only [hlam, p5299_0]
                        · linarith only [h5290, hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h0, hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h4669, hlam, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h4671, hlam, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h4673, hlam, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h1, hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h4675, hc12, hc34, hlam, hphi, ht23, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h4675, hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h5251, hlam, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h2, hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h2, h4173, hc12, hc45, hlam, hphi, ht23, ht34, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h4172, h4173, h4675, hc13, hc45, hlam, hphi, ht34, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h5253, hlam, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h3, hlam, p5261_0]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h5251, h5256, hc12, hc23, hlam, hphi, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h4669, h5251, h5256, hc12, hc23, hlam, hphi, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [h4671, h5251, h5256, hc12, hc23, hlam, hphi, p5261_1]
                      · have p5261_0 := h5261c.1
                        have p5261_1 := h5261c.2.1
                        have p5261_2 := h5261c.2.2.1
                        have p5261_3 := h5261c.2.2.2
                        linarith only [hlam, p5261_0]
                · linarith only [h4, h4172, h4669, h4675, h5256, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h4, h4172, h5255, hlam]

set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3686 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4101 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4172 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h4173 | h4173
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h3686 h4101 h4172 h4173
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h3686 h4101 h4172 h4173

end R2N4
