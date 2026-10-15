import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h636 | h636
  · rcases m.htr 1 2 4 (by decide) (by decide) with h637 | h637
    · rcases m.htr 1 2 5 (by decide) (by decide) with h638 | h638
      · rcases m.htr 1 3 4 (by decide) (by decide) with h639 | h639
        · rcases m.htr 1 3 5 (by decide) (by decide) with h640 | h640
          · rcases m.htr 1 4 5 (by decide) (by decide) with h641 | h641
            · linarith only [h2, h641, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
              · linarith only [h0, h636, h643, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h645 | h645
                · linarith only [h639, h643, h645, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h647 | h647
                  · linarith only [h0, h2, h5, h639, h643, h647, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h649 | h649
                    · linarith only [h2, h639, h649, h8, hlam]
                    · rcases h1bigk with h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h637, hc01, hlam, hphi, ht0b, ht45, ht5b, p651_1, u4ehi2]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h639, h643, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        rcases p651_3 (m.d 0 1) (by simp) with h655 | h655
                        · rcases p651_3 (m.d 1 2) (by simp) with h656 | h656
                          · linarith only [h0, h656, hlam]
                          · linarith only [h637, h656, hlam]
                        · linarith only [h655, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        rcases p651_3 (m.d 0 1) (by simp) with h660 | h660
                        · rcases p651_3 (m.d 1 2) (by simp) with h661 | h661
                          · linarith only [h0, h661, hlam]
                          · linarith only [h638, h661, hlam]
                        · linarith only [h660, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h0, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h640, h645, h647, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p651_1, u4ehi2]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h0, h639, h643, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h0, h639, h641, h643, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h1, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h636, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h1, h639, h643, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h0, h636, h639, h641, h643, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h2, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h637, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h639, hlam, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h641, hlam, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h3, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h638, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h640, hlam, p651_0]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [h3, h639, h643, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p651_1]
                      · have p651_0 := h651c.1
                        have p651_1 := h651c.2.1
                        have p651_2 := h651c.2.2.1
                        have p651_3 := h651c.2.2.2
                        linarith only [hlam, p651_0]
          · linarith only [h0, h4, h639, h640, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h686 | h686
          · rcases m.htr 1 4 5 (by decide) (by decide) with h687 | h687
            · linarith only [h2, h687, h8, hlam]
            · linarith only [h639, h686, h687, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h690 | h690
            · linarith only [h2, h690, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h692 | h692
              · linarith only [h636, h639, h692, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h694 | h694
                · linarith only [h636, h686, h694, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h696 | h696
                  · linarith only [h0, h5, h696, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h698 | h698
                    · linarith only [h698, h7, h8, hlam]
                    · rcases h1bigk with h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h637, hc01, hlam, hphi, ht0b, ht45, ht5b, p700_1, u4ehi2]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        rcases p700_3 (m.d 0 1) (by simp) with h703 | h703
                        · rcases p700_3 (m.d 1 2) (by simp) with h704 | h704
                          · linarith only [h0, h704, hlam]
                          · linarith only [h636, h704, hlam]
                        · linarith only [h703, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        rcases p700_3 (m.d 0 1) (by simp) with h708 | h708
                        · rcases p700_3 (m.d 1 2) (by simp) with h709 | h709
                          · linarith only [h0, h709, hlam]
                          · linarith only [h637, h709, hlam]
                        · linarith only [h708, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        rcases p700_3 (m.d 0 1) (by simp) with h713 | h713
                        · rcases p700_3 (m.d 1 2) (by simp) with h714 | h714
                          · linarith only [h0, h714, hlam]
                          · linarith only [h638, h714, hlam]
                        · linarith only [h713, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h0, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        rcases p700_3 (m.d 0 1) (by simp) with h720 | h720
                        · rcases p700_3 (m.d 1 2) (by simp) with h721 | h721
                          · rcases p700_3 (m.d 1 3) (by simp) with h722 | h722
                            · linarith only [h636, h722, hlam]
                            · rcases p700_3 (m.d 1 4) (by simp) with h724 | h724
                              · linarith only [h637, h724, hlam]
                              · linarith only [h639, h724, hlam]
                          · linarith only [h636, h721, hlam]
                        · linarith only [h1, h720, hlam]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h0, h637, hc01, hlam, hphi, ht0b, ht45, ht5b, p700_1, u4ehi2]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p700_1, u5ehi1]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h1, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h636, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h639, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h686, hlam, p700_1]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h2, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h637, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h2, h8, hc13, hc45, hlam, hphi, ht34, p700_1]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h690, hlam, p700_1]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h3, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h638, hlam, p700_0]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        rcases p700_3 (m.d 0 1) (by simp) with h743 | h743
                        · rcases p700_3 (m.d 1 2) (by simp) with h744 | h744
                          · rcases p700_3 (m.d 1 3) (by simp) with h745 | h745
                            · linarith only [h686, h745, hlam]
                            · rcases p700_3 (m.d 1 4) (by simp) with h747 | h747
                              · linarith only [h690, h747, hlam]
                              · linarith only [h639, h747, hlam]
                          · linarith only [h636, h744, hlam]
                        · linarith only [h1, h743, hlam]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [h0, h4, h686, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p700_1, u4ehi1]
                      · have p700_0 := h700c.1
                        have p700_1 := h700c.2.1
                        have p700_2 := h700c.2.2.1
                        have p700_3 := h700c.2.2.2
                        linarith only [hlam, p700_0]
      · linarith only [h0, h6, h637, h638, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
    · linarith only [h5, h636, h637, h8, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h756 | h756
    · linarith only [h4, h636, h756, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h758 | h758
      · linarith only [h5, h756, h758, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h760 | h760
        · rcases m.htr 1 3 5 (by decide) (by decide) with h761 | h761
          · rcases m.htr 1 4 5 (by decide) (by decide) with h762 | h762
            · linarith only [h2, h762, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h764 | h764
              · rcases m.htr 2 3 5 (by decide) (by decide) with h765 | h765
                · rcases m.htr 2 4 5 (by decide) (by decide) with h766 | h766
                  · linarith only [h5, h766, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h768 | h768
                    · linarith only [h5, h756, h760, h768, h8, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        rcases p770_3 (m.d 0 1) (by simp) with h772 | h772
                        · rcases p770_3 (m.d 1 2) (by simp) with h773 | h773
                          · linarith only [h773, hlam, p770_0]
                          · rcases p770_3 (m.d 1 3) (by simp) with h775 | h775
                            · linarith only [h1, h775, hlam]
                            · linarith only [h636, h775, hlam]
                        · linarith only [h772, hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h761, h768, hc01, hlam, hphi, ht0b, ht45, ht5b, p770_1, u4ehi3]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        rcases p770_3 (m.d 0 1) (by simp) with h780 | h780
                        · rcases p770_3 (m.d 1 2) (by simp) with h781 | h781
                          · linarith only [h0, h781, hlam]
                          · rcases p770_3 (m.d 1 3) (by simp) with h783 | h783
                            · linarith only [h1, h783, hlam]
                            · linarith only [h760, h783, hlam]
                        · linarith only [h780, hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        rcases p770_3 (m.d 0 1) (by simp) with h787 | h787
                        · rcases p770_3 (m.d 1 2) (by simp) with h788 | h788
                          · linarith only [h0, h788, hlam]
                          · rcases p770_3 (m.d 1 3) (by simp) with h790 | h790
                            · linarith only [h1, h790, hlam]
                            · linarith only [h761, h790, hlam]
                        · linarith only [h787, hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h0, hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h636, hlam, p770_1]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h756, hlam, p770_1]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h758, hlam, p770_1]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h1, hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        rcases p770_3 (m.d 0 1) (by simp) with h800 | h800
                        · rcases p770_3 (m.d 1 2) (by simp) with h801 | h801
                          · linarith only [h636, h801, hlam]
                          · rcases p770_3 (m.d 1 3) (by simp) with h803 | h803
                            · rcases p770_3 (m.d 1 4) (by simp) with h804 | h804
                              · linarith only [h760, h804, hlam]
                              · linarith only [h756, h804, hlam]
                            · linarith only [h636, h803, hlam]
                        · linarith only [h0, h800, hlam]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h0, h4, h636, hc01, hlam, hphi, ht0b, ht45, ht5b, p770_1, u4ehi1]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h0, h4, h636, hc01, hlam, hphi, ht0b, ht5b, p770_1, u5ehi1]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h2, hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h2, h8, hc12, hc45, hlam, hphi, ht23, ht34, p770_1]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h760, hlam, p770_1]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h762, hlam, p770_1]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h3, hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        rcases p770_3 (m.d 0 1) (by simp) with h818 | h818
                        · rcases p770_3 (m.d 1 2) (by simp) with h819 | h819
                          · linarith only [h758, h819, hlam]
                          · rcases p770_3 (m.d 1 3) (by simp) with h821 | h821
                            · rcases p770_3 (m.d 1 4) (by simp) with h822 | h822
                              · linarith only [h762, h822, hlam]
                              · linarith only [h756, h822, hlam]
                            · linarith only [h636, h821, hlam]
                        · linarith only [h0, h818, hlam]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h761, hlam, p770_0]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [h0, h4, h636, h761, hc01, hlam, hphi, ht0b, ht45, ht5b, p770_1, u4ehi1]
                      · have p770_0 := h770c.1
                        have p770_1 := h770c.2.1
                        have p770_2 := h770c.2.2.1
                        have p770_3 := h770c.2.2.2
                        linarith only [hlam, p770_0]
                · linarith only [h0, h4, h636, h7, h760, h765, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h636, h760, h764, hlam]
          · linarith only [h0, h4, h7, h760, h761, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h833 | h833
          · rcases m.htr 1 4 5 (by decide) (by decide) with h834 | h834
            · linarith only [h5, h756, h8, h834, hlam]
            · linarith only [h760, h833, h834, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h837 | h837
            · linarith only [h5, h756, h8, h837, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h839 | h839
              · rcases m.htr 2 3 5 (by decide) (by decide) with h840 | h840
                · rcases m.htr 2 4 5 (by decide) (by decide) with h841 | h841
                  · linarith only [h5, h8, h841, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h843 | h843
                    · linarith only [h0, h4, h8, h839, h843, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h1bigk with h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h0, h4, h636, h833, h840, hlam, p845_2]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h0, h4, h833, h840, hlam, p845_2]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        rcases p845_3 (m.d 0 1) (by simp) with h849 | h849
                        · rcases p845_3 (m.d 1 2) (by simp) with h850 | h850
                          · linarith only [h0, h850, hlam]
                          · rcases p845_3 (m.d 1 3) (by simp) with h852 | h852
                            · linarith only [h1, h852, hlam]
                            · rcases p845_3 (m.d 1 4) (by simp) with h854 | h854
                              · linarith only [h854, hlam, p845_0]
                              · rcases p845_3 (m.d 1 5) (by simp) with h856 | h856
                                · linarith only [h3, h856, hlam]
                                · linarith only [h837, h856, hlam]
                        · linarith only [h849, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        rcases p845_3 (m.d 0 1) (by simp) with h860 | h860
                        · rcases p845_3 (m.d 1 2) (by simp) with h861 | h861
                          · linarith only [h0, h861, hlam]
                          · rcases p845_3 (m.d 1 3) (by simp) with h863 | h863
                            · linarith only [h1, h863, hlam]
                            · rcases p845_3 (m.d 1 4) (by simp) with h865 | h865
                              · linarith only [h2, h865, hlam]
                              · rcases p845_3 (m.d 1 5) (by simp) with h867 | h867
                                · linarith only [h867, hlam, p845_0]
                                · rcases h2bigk with h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h4, h636, h760, h840, h843, hlam, p869_2]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h0, h636, h760, h840, h843, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p869_1]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    rcases p869_3 (m.d 0 2) (by simp) with h873 | h873
                                    · rcases p869_3 (m.d 1 2) (by simp) with h874 | h874
                                      · linarith only [h0, h874, hlam]
                                      · rcases p869_3 (m.d 2 3) (by simp) with h876 | h876
                                        · linarith only [h4, h876, hlam]
                                        · linarith only [h839, h876, hlam]
                                    · linarith only [h873, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    rcases p869_3 (m.d 0 2) (by simp) with h880 | h880
                                    · rcases p869_3 (m.d 1 2) (by simp) with h881 | h881
                                      · linarith only [h0, h881, hlam]
                                      · rcases p869_3 (m.d 2 3) (by simp) with h883 | h883
                                        · linarith only [h4, h883, hlam]
                                        · linarith only [h840, h883, hlam]
                                    · linarith only [h880, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h0, hlam, p869_1]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h636, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h756, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h758, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h4, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    rcases p869_3 (m.d 0 2) (by simp) with h893 | h893
                                    · rcases p869_3 (m.d 1 2) (by simp) with h894 | h894
                                      · linarith only [h894, hlam, p869_0]
                                      · rcases p869_3 (m.d 2 3) (by simp) with h896 | h896
                                        · rcases p869_3 (m.d 2 4) (by simp) with h897 | h897
                                          · linarith only [h839, h897, hlam]
                                          · linarith only [h756, h897, hlam]
                                        · linarith only [h896, hlam, p869_0]
                                    · linarith only [h0, h893, hlam]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h636, h760, h839, hc12, hc23, hlam, hphi, p869_1]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p869_1, u5ehi2]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h5, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p869_1]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h839, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h841, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h6, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    rcases p869_3 (m.d 0 2) (by simp) with h911 | h911
                                    · rcases p869_3 (m.d 1 2) (by simp) with h912 | h912
                                      · linarith only [h912, hlam, p869_0]
                                      · rcases p869_3 (m.d 2 3) (by simp) with h914 | h914
                                        · rcases p869_3 (m.d 2 4) (by simp) with h915 | h915
                                          · linarith only [h841, h915, hlam]
                                          · linarith only [h756, h915, hlam]
                                        · linarith only [h636, h914, hlam]
                                    · linarith only [h0, h911, hlam]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h840, hlam, p869_0]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p869_1, u4ehi2]
                                  · have p869_0 := h869c.1
                                    have p869_1 := h869c.2.1
                                    have p869_2 := h869c.2.2.1
                                    have p869_3 := h869c.2.2.2
                                    linarith only [hlam, p869_0]
                        · linarith only [h860, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h0, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h636, hlam, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h756, hlam, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h758, hlam, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h1, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h760, hc12, hc34, hlam, hphi, ht23, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h760, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h833, hlam, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h2, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h2, h8, hc12, hc45, hlam, hphi, ht23, ht34, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h5, h756, h8, hc13, hc45, hlam, hphi, ht34, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h837, hlam, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h3, hlam, p845_0]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h0, h4, h833, h840, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h0, h4, h636, h833, h840, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p845_1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [h0, h4, h833, h840, hc01, hlam, hphi, ht0b, ht45, ht5b, p845_1, u4ehi1]
                      · have p845_0 := h845c.1
                        have p845_1 := h845c.2.1
                        have p845_2 := h845c.2.2.1
                        have p845_3 := h845c.2.2.2
                        linarith only [hlam, p845_0]
                · linarith only [h0, h4, h7, h839, h840, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h945 | h945
                · linarith only [h5, h636, h8, h833, h839, h945, hc12, hc45, hlam, hphi, ht23, ht34]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h947 | h947
                  · linarith only [h5, h8, h947, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h949 | h949
                    · linarith only [h636, h7, h8, h945, h949, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h636, h839, h949, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h952 | h952
  · rcases m.htr 1 2 3 (by decide) (by decide) with h953 | h953
    · rcases m.htr 1 2 4 (by decide) (by decide) with h954 | h954
      · rcases m.htr 1 2 5 (by decide) (by decide) with h955 | h955
        · rcases m.htr 1 3 4 (by decide) (by decide) with h956 | h956
          · rcases m.htr 1 3 5 (by decide) (by decide) with h957 | h957
            · linarith only [h1, h7, h957, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h959 | h959
              · linarith only [h956, h957, h959, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h961 | h961
                · linarith only [h0, h953, h961, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · linarith only [h1, h7, h956, h961, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h964 | h964
            · linarith only [h1, h7, h964, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h966 | h966
              · rcases m.htr 2 3 4 (by decide) (by decide) with h967 | h967
                · linarith only [h4, h7, h956, h967, hc13, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h969 | h969
                  · linarith only [h1, h7, h953, h969, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h971 | h971
                    · linarith only [h0, h954, h971, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h0, h954, h966, h971, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h974 | h974
                · linarith only [h4, h7, h956, h974, hc13, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h976 | h976
                  · linarith only [h7, h953, h956, h976, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h978 | h978
                    · linarith only [h0, h5, h966, h978, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h980 | h980
                      · rcases h1bigk with h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h955, hc01, hlam, hphi, ht0b, ht5b, p981_1, u5ehi2]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          rcases p981_3 (m.d 0 1) (by simp) with h984 | h984
                          · rcases p981_3 (m.d 1 2) (by simp) with h985 | h985
                            · linarith only [h0, h985, hlam]
                            · linarith only [h953, h985, hlam]
                          · linarith only [h984, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          rcases p981_3 (m.d 0 1) (by simp) with h989 | h989
                          · rcases p981_3 (m.d 1 2) (by simp) with h990 | h990
                            · linarith only [h0, h990, hlam]
                            · linarith only [h954, h990, hlam]
                          · linarith only [h989, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          rcases p981_3 (m.d 0 1) (by simp) with h994 | h994
                          · rcases p981_3 (m.d 1 2) (by simp) with h995 | h995
                            · linarith only [h0, h995, hlam]
                            · linarith only [h955, h995, hlam]
                          · linarith only [h994, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h0, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          rcases p981_3 (m.d 0 1) (by simp) with h1001 | h1001
                          · rcases p981_3 (m.d 1 2) (by simp) with h1002 | h1002
                            · rcases p981_3 (m.d 1 3) (by simp) with h1003 | h1003
                              · linarith only [h1003, h953, hlam]
                              · rcases p981_3 (m.d 1 4) (by simp) with h1005 | h1005
                                · linarith only [h1005, h954, hlam]
                                · linarith only [h1005, h956, hlam]
                            · linarith only [h1002, h953, hlam]
                          · linarith only [h1, h1001, hlam]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h0, h954, hc01, hlam, hphi, ht0b, ht45, ht5b, p981_1, u4ehi2]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h0, h954, h966, hc01, hlam, hphi, ht0b, ht45, ht5b, p981_1, u4ehi2]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h1, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h953, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h956, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h964, hlam, p981_1]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h2, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h954, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h966, h980, hc13, hc34, hlam, hphi, p981_1]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h966, hlam, p981_1]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h3, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h955, hlam, p981_0]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h953, h966, h980, hc23, hc34, hlam, hphi, p981_1]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [h954, h966, h980, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p981_1, u4ehi2]
                        · have p981_0 := h981c.1
                          have p981_1 := h981c.2.1
                          have p981_2 := h981c.2.2.1
                          have p981_3 := h981c.2.2.2
                          linarith only [hlam, p981_0]
                      · linarith only [h7, h952, h980, hlam]
        · linarith only [h0, h6, h954, h955, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1029 | h1029
        · linarith only [h0, h1029, h5, h954, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1031 | h1031
          · linarith only [h0, h1031, h5, h953, h954, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1033 | h1033
            · linarith only [h0, h1033, h5, h7, h953, h954, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1035 | h1035
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1036 | h1036
                · linarith only [h1, h1031, h1035, h1036, h953, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1038 | h1038
                  · linarith only [h0, h1038, h5, h7, h953, h954, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1040 | h1040
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1041 | h1041
                      · rcases h1bigk with h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          rcases p1042_3 (m.d 0 1) (by simp) with h1044 | h1044
                          · rcases p1042_3 (m.d 1 2) (by simp) with h1045 | h1045
                            · linarith only [h1045, hlam, p1042_0]
                            · rcases p1042_3 (m.d 1 3) (by simp) with h1047 | h1047
                              · linarith only [h1, h1047, hlam]
                              · rcases p1042_3 (m.d 1 4) (by simp) with h1049 | h1049
                                · linarith only [h1049, h2, hlam]
                                · linarith only [h1049, h954, hlam]
                          · linarith only [h1044, hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          rcases p1042_3 (m.d 0 1) (by simp) with h1053 | h1053
                          · rcases p1042_3 (m.d 1 2) (by simp) with h1054 | h1054
                            · linarith only [h0, h1054, hlam]
                            · linarith only [h1054, h953, hlam]
                          · linarith only [h1053, hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h1035, hc01, hlam, hphi, ht0b, ht45, ht5b, p1042_1, u4ehi4]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          rcases p1042_3 (m.d 0 1) (by simp) with h1059 | h1059
                          · rcases p1042_3 (m.d 1 2) (by simp) with h1060 | h1060
                            · linarith only [h0, h1060, hlam]
                            · rcases p1042_3 (m.d 1 3) (by simp) with h1062 | h1062
                              · linarith only [h1, h1062, hlam]
                              · rcases p1042_3 (m.d 1 4) (by simp) with h1064 | h1064
                                · linarith only [h1064, h2, hlam]
                                · linarith only [h1035, h1064, hlam]
                          · linarith only [h1059, hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h0, hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h0, h1029, h1040, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1042_1]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h954, hlam, p1042_1]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h1029, hlam, p1042_1]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h1, hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h953, hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h1031, hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h1033, hlam, p1042_1]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h2, hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h2, h953, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1042_1]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          rcases p1042_3 (m.d 0 1) (by simp) with h1080 | h1080
                          · rcases p1042_3 (m.d 1 2) (by simp) with h1081 | h1081
                            · linarith only [h1081, h954, hlam]
                            · linarith only [h1081, h953, hlam]
                          · linarith only [h1, h1080, hlam]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h0, h1029, h5, h953, h954, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1042_1]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h3, hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h3, h953, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1042_1]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          rcases p1042_3 (m.d 0 1) (by simp) with h1089 | h1089
                          · rcases p1042_3 (m.d 1 2) (by simp) with h1090 | h1090
                            · linarith only [h1029, h1090, hlam]
                            · linarith only [h1090, h953, hlam]
                          · linarith only [h1, h1089, hlam]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [h1035, hlam, p1042_0]
                        · have p1042_0 := h1042c.1
                          have p1042_1 := h1042c.2.1
                          have p1042_2 := h1042c.2.2.1
                          have p1042_3 := h1042c.2.2.2
                          linarith only [hlam, p1042_0]
                      · linarith only [h1031, h1035, h1041, hlam]
                    · linarith only [h0, h1040, h5, h952, h953, h954, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1098 | h1098
                · linarith only [h1031, h1098, h953, h954, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1100 | h1100
                  · linarith only [h1100, h7, h953, h954, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1102 | h1102
                    · linarith only [h0, h1035, h1102, h5, h953, h954, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1102, h953, h954, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1105 | h1105
      · linarith only [h1105, h4, h7, h953, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1107 | h1107
        · linarith only [h1107, h4, h7, h953, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1109 | h1109
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1110 | h1110
            · linarith only [h1, h1110, h4, h7, h953, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1112 | h1112
              · linarith only [h1109, h1110, h1112, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1114 | h1114
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1115 | h1115
                  · linarith only [h1115, h4, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1117 | h1117
                    · linarith only [h0, h1112, h1117, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1119 | h1119
                      · linarith only [h1109, h1117, h1119, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h1109, h1119, h4, h7, h953, hc45, hlam, hphi, u4ehi3]
                · linarith only [h1109, h1114, h953, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1123 | h1123
            · linarith only [h1109, h1123, h7, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1125 | h1125
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1126 | h1126
                · linarith only [h1109, h1126, h4, h7, hc13, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1128 | h1128
                  · linarith only [h1128, h4, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1130 | h1130
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1131 | h1131
                      · rcases h1bigk with h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          rcases p1132_3 (m.d 0 1) (by simp) with h1134 | h1134
                          · rcases p1132_3 (m.d 1 2) (by simp) with h1135 | h1135
                            · linarith only [h1135, hlam, p1132_0]
                            · rcases p1132_3 (m.d 1 3) (by simp) with h1137 | h1137
                              · linarith only [h1, h1137, hlam]
                              · linarith only [h1137, h953, hlam]
                          · linarith only [h1134, hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          rcases p1132_3 (m.d 0 1) (by simp) with h1141 | h1141
                          · rcases p1132_3 (m.d 1 2) (by simp) with h1142 | h1142
                            · linarith only [h0, h1142, hlam]
                            · rcases p1132_3 (m.d 1 3) (by simp) with h1144 | h1144
                              · linarith only [h1144, hlam, p1132_0]
                              · rcases p1132_3 (m.d 1 4) (by simp) with h1146 | h1146
                                · linarith only [h1146, h2, hlam]
                                · linarith only [h1109, h1146, hlam]
                          · linarith only [h1141, hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h1125, hc01, hlam, hphi, ht0b, ht45, ht5b, p1132_1, u4ehi4]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          rcases p1132_3 (m.d 0 1) (by simp) with h1151 | h1151
                          · rcases p1132_3 (m.d 1 2) (by simp) with h1152 | h1152
                            · linarith only [h0, h1152, hlam]
                            · rcases p1132_3 (m.d 1 3) (by simp) with h1154 | h1154
                              · linarith only [h1, h1154, hlam]
                              · rcases p1132_3 (m.d 1 4) (by simp) with h1156 | h1156
                                · linarith only [h1156, h2, hlam]
                                · linarith only [h1125, h1156, hlam]
                          · linarith only [h1151, hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h0, hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h953, hlam, p1132_1]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h1105, hlam, p1132_1]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h1107, hlam, p1132_1]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h1, hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h1, h1131, h7, hc12, hc34, hlam, hphi, ht23, p1132_1]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h1109, hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h1123, hlam, p1132_1]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h2, hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          rcases p1132_3 (m.d 0 1) (by simp) with h1171 | h1171
                          · rcases p1132_3 (m.d 1 2) (by simp) with h1172 | h1172
                            · linarith only [h1105, h1172, hlam]
                            · rcases p1132_3 (m.d 1 3) (by simp) with h1174 | h1174
                              · linarith only [h1109, h1174, hlam]
                              · linarith only [h1174, h953, hlam]
                          · linarith only [h0, h1171, hlam]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          rcases p1132_3 (m.d 0 1) (by simp) with h1178 | h1178
                          · rcases p1132_3 (m.d 1 2) (by simp) with h1179 | h1179
                            · linarith only [h1105, h1179, hlam]
                            · rcases p1132_3 (m.d 1 3) (by simp) with h1181 | h1181
                              · linarith only [h1109, h1181, hlam]
                              · rcases p1132_3 (m.d 1 4) (by simp) with h1183 | h1183
                                · rcases p1132_3 (m.d 1 5) (by simp) with h1184 | h1184
                                  · linarith only [h1125, h1184, hlam]
                                  · linarith only [h1123, h1184, hlam]
                                · linarith only [h1109, h1183, hlam]
                          · linarith only [h1, h1178, hlam]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h1125, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1132_1, u4ehi4]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h3, hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          rcases p1132_3 (m.d 0 1) (by simp) with h1192 | h1192
                          · rcases p1132_3 (m.d 1 2) (by simp) with h1193 | h1193
                            · linarith only [h1107, h1193, hlam]
                            · rcases p1132_3 (m.d 1 3) (by simp) with h1195 | h1195
                              · linarith only [h1123, h1195, hlam]
                              · linarith only [h1195, h953, hlam]
                          · linarith only [h0, h1192, hlam]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          rcases p1132_3 (m.d 0 1) (by simp) with h1199 | h1199
                          · rcases p1132_3 (m.d 1 2) (by simp) with h1200 | h1200
                            · linarith only [h1107, h1200, hlam]
                            · rcases p1132_3 (m.d 1 3) (by simp) with h1202 | h1202
                              · linarith only [h1123, h1202, hlam]
                              · rcases p1132_3 (m.d 1 4) (by simp) with h1204 | h1204
                                · rcases p1132_3 (m.d 1 5) (by simp) with h1205 | h1205
                                  · rcases h2bigk with h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h1107, h1130, h5, h953, hlam, p1132_1, p1206_2]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      rcases p1206_3 (m.d 0 2) (by simp) with h1209 | h1209
                                      · rcases p1206_3 (m.d 1 2) (by simp) with h1210 | h1210
                                        · linarith only [h0, h1210, hlam]
                                        · rcases p1206_3 (m.d 2 3) (by simp) with h1212 | h1212
                                          · linarith only [h1212, hlam, p1206_0]
                                          · rcases p1206_3 (m.d 2 4) (by simp) with h1214 | h1214
                                            · linarith only [h1214, h5, hlam]
                                            · linarith only [h1126, h1214, hlam]
                                      · linarith only [h1209, hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h0, h1107, h1130, h953, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1132_1, p1206_1]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h0, h1107, h953, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1132_1, p1206_1]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h0, hlam, p1206_1]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h953, hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h1105, hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h1107, hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h4, hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h1131, h4, h7, hc12, hc34, hlam, hphi, ht23, p1206_1]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h1126, hlam, p1206_1]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h1128, hlam, p1206_1]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h5, hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      rcases p1206_3 (m.d 0 2) (by simp) with h1231 | h1231
                                      · rcases p1206_3 (m.d 1 2) (by simp) with h1232 | h1232
                                        · linarith only [h1232, hlam, p1206_0]
                                        · rcases p1206_3 (m.d 2 3) (by simp) with h1234 | h1234
                                          · linarith only [h1126, h1234, hlam]
                                          · linarith only [h1234, h953, hlam]
                                      · linarith only [h0, h1231, hlam]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h953, hc12, hc24, hlam, hphi, p1206_1]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h0, h1107, h5, h953, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1132_1, p1206_1]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h6, hlam, p1206_0]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      rcases p1206_3 (m.d 0 2) (by simp) with h1242 | h1242
                                      · rcases p1206_3 (m.d 1 2) (by simp) with h1243 | h1243
                                        · linarith only [h1243, hlam, p1206_0]
                                        · rcases p1206_3 (m.d 2 3) (by simp) with h1245 | h1245
                                          · linarith only [h1128, h1245, hlam]
                                          · linarith only [h1245, h953, hlam]
                                      · linarith only [h0, h1242, hlam]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h953, hc12, hc25, hlam, hphi, p1206_1]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [h1130, hlam, p1206_1]
                                    · have p1206_0 := h1206c.1
                                      have p1206_1 := h1206c.2.1
                                      have p1206_2 := h1206c.2.2.1
                                      have p1206_3 := h1206c.2.2.2
                                      linarith only [hlam, p1206_0]
                                  · linarith only [h1123, h1205, hlam]
                                · linarith only [h1109, h1204, hlam]
                          · linarith only [h1, h1199, hlam]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [h1125, hlam, p1132_0]
                        · have p1132_0 := h1132c.1
                          have p1132_1 := h1132c.2.1
                          have p1132_2 := h1132c.2.2.1
                          have p1132_3 := h1132c.2.2.2
                          linarith only [hlam, p1132_0]
                      · linarith only [h1109, h1125, h1131, hlam]
                    · linarith only [h1125, h1130, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1259 | h1259
                · linarith only [h1109, h1259, h4, h7, h953, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1261 | h1261
                  · linarith only [h1261, h4, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1263 | h1263
                    · linarith only [h0, h1125, h1263, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1265 | h1265
                      · linarith only [h1259, h1263, h1265, h953, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1259, h1265, h953, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1268 | h1268
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1269 | h1269
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1270 | h1270
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1271 | h1271
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1272 | h1272
            · linarith only [h1, h1272, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1274 | h1274
              · linarith only [h1274, h2, h952, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1276 | h1276
                · linarith only [h0, h1268, h1276, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · linarith only [h1, h1271, h1276, h7, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1279 | h1279
            · linarith only [h1271, h1279, h7, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1281 | h1281
              · linarith only [h1281, h2, h952, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1283 | h1283
                · linarith only [h0, h1268, h1283, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1285 | h1285
                  · linarith only [h1, h1268, h1285, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1287 | h1287
                    · linarith only [h0, h1287, h2, h5, h952, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1289 | h1289
                      · rcases h1bigk with h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1270, hc01, hlam, hphi, ht0b, ht5b, p1290_1, u5ehi2]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          rcases p1290_3 (m.d 0 1) (by simp) with h1293 | h1293
                          · rcases p1290_3 (m.d 1 2) (by simp) with h1294 | h1294
                            · linarith only [h0, h1294, hlam]
                            · linarith only [h1268, h1294, hlam]
                          · linarith only [h1293, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          rcases p1290_3 (m.d 0 1) (by simp) with h1298 | h1298
                          · rcases p1290_3 (m.d 1 2) (by simp) with h1299 | h1299
                            · linarith only [h0, h1299, hlam]
                            · linarith only [h1269, h1299, hlam]
                          · linarith only [h1298, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          rcases p1290_3 (m.d 0 1) (by simp) with h1303 | h1303
                          · rcases p1290_3 (m.d 1 2) (by simp) with h1304 | h1304
                            · linarith only [h0, h1304, hlam]
                            · linarith only [h1270, h1304, hlam]
                          · linarith only [h1303, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h0, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          rcases p1290_3 (m.d 0 1) (by simp) with h1310 | h1310
                          · rcases p1290_3 (m.d 1 2) (by simp) with h1311 | h1311
                            · rcases p1290_3 (m.d 1 3) (by simp) with h1312 | h1312
                              · linarith only [h1268, h1312, hlam]
                              · rcases p1290_3 (m.d 1 4) (by simp) with h1314 | h1314
                                · linarith only [h1269, h1314, hlam]
                                · linarith only [h1271, h1314, hlam]
                            · linarith only [h1268, h1311, hlam]
                          · linarith only [h1, h1310, hlam]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h0, h1269, hc01, hlam, hphi, ht0b, ht45, ht5b, p1290_1, u4ehi2]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1290_1, u5ehi1]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1268, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1271, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1279, hlam, p1290_1]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h2, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1269, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1289, h2, h952, hc13, hc34, hlam, hphi, p1290_1]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1281, hlam, p1290_1]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h3, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1270, hlam, p1290_0]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1268, h1289, h3, h952, hc23, hc34, hlam, hphi, p1290_1]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [h1289, h3, h952, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1290_1, u4ehi1]
                        · have p1290_0 := h1290c.1
                          have p1290_1 := h1290c.2.1
                          have p1290_2 := h1290c.2.2.1
                          have p1290_3 := h1290c.2.2.2
                          linarith only [hlam, p1290_0]
                      · rcases h1bigk with h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h1269, hc01, hlam, hphi, ht0b, ht45, ht5b, p1336_1, u4ehi2]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          rcases p1336_3 (m.d 0 1) (by simp) with h1339 | h1339
                          · rcases p1336_3 (m.d 1 2) (by simp) with h1340 | h1340
                            · linarith only [h0, h1340, hlam]
                            · linarith only [h1268, h1340, hlam]
                          · linarith only [h1339, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          rcases p1336_3 (m.d 0 1) (by simp) with h1344 | h1344
                          · rcases p1336_3 (m.d 1 2) (by simp) with h1345 | h1345
                            · linarith only [h0, h1345, hlam]
                            · linarith only [h1269, h1345, hlam]
                          · linarith only [h1344, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          rcases p1336_3 (m.d 0 1) (by simp) with h1349 | h1349
                          · rcases p1336_3 (m.d 1 2) (by simp) with h1350 | h1350
                            · linarith only [h0, h1350, hlam]
                            · linarith only [h1270, h1350, hlam]
                          · linarith only [h1349, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h0, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          rcases p1336_3 (m.d 0 1) (by simp) with h1356 | h1356
                          · rcases p1336_3 (m.d 1 2) (by simp) with h1357 | h1357
                            · rcases p1336_3 (m.d 1 3) (by simp) with h1358 | h1358
                              · linarith only [h1268, h1358, hlam]
                              · rcases p1336_3 (m.d 1 4) (by simp) with h1360 | h1360
                                · linarith only [h1269, h1360, hlam]
                                · linarith only [h1271, h1360, hlam]
                            · linarith only [h1268, h1357, hlam]
                          · linarith only [h1, h1356, hlam]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h0, h1269, hc01, hlam, hphi, ht0b, ht45, ht5b, p1336_1, u4ehi2]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1336_1, u5ehi1]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h1, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h1268, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h1271, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h1279, hlam, p1336_1]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h2, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h1269, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h1268, h2, h952, hc23, hc45, hlam, hphi, ht34, p1336_1]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h1281, hlam, p1336_1]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h3, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h1270, hlam, p1336_0]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          rcases p1336_3 (m.d 0 1) (by simp) with h1379 | h1379
                          · rcases p1336_3 (m.d 1 2) (by simp) with h1380 | h1380
                            · rcases p1336_3 (m.d 1 3) (by simp) with h1381 | h1381
                              · linarith only [h1279, h1381, hlam]
                              · rcases p1336_3 (m.d 1 4) (by simp) with h1383 | h1383
                                · linarith only [h1281, h1383, hlam]
                                · linarith only [h1271, h1383, hlam]
                            · linarith only [h1268, h1380, hlam]
                          · linarith only [h1, h1379, hlam]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1336_1, u4ehi1]
                        · have p1336_0 := h1336c.1
                          have p1336_1 := h1336c.2.1
                          have p1336_2 := h1336c.2.2.1
                          have p1336_3 := h1336c.2.2.2
                          linarith only [hlam, p1336_0]
        · linarith only [h0, h1269, h1270, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · linarith only [h1268, h1269, h5, h952, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1392 | h1392
      · linarith only [h1268, h1392, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1394 | h1394
        · linarith only [h1392, h1394, h5, h952, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1396 | h1396
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1397 | h1397
            · linarith only [h1268, h1397, h4, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1399 | h1399
              · linarith only [h1392, h1399, h2, h5, h952, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1401 | h1401
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1402 | h1402
                  · linarith only [h1402, h4, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1404 | h1404
                    · linarith only [h0, h1268, h1396, h1404, h4, h5, h7, h952, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1406 | h1406
                      · linarith only [h1268, h1392, h1396, h1406, h4, h5, h7, h952, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1268, h1396, h1406, h4, h7, hc45, hlam, hphi, u4ehi3]
                · linarith only [h1268, h1396, h1401, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1410 | h1410
            · linarith only [h1396, h1410, h7, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1412 | h1412
              · linarith only [h1392, h1412, h5, h952, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1414 | h1414
                · linarith only [h1396, h1414, h4, h7, hc13, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1416 | h1416
                  · linarith only [h1416, h4, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1418 | h1418
                    · linarith only [h1418, h5, h952, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1420 | h1420
                      · linarith only [h1268, h1414, h1420, h5, h952, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1268, h1414, h1420, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h1423 | h1423
  · linarith only [h1423, h4, h6, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1425 | h1425
    · linarith only [h1425, h5, h6, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1427 | h1427
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1428 | h1428
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1429 | h1429
          · linarith only [h0, h1429, h6, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1431 | h1431
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1432 | h1432
              · linarith only [h1, h1423, h1432, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1434 | h1434
                · linarith only [h1425, h1434, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1436 | h1436
                  · linarith only [h1436, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h1, h1423, h1431, h1436, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1439 | h1439
              · linarith only [h1, h1423, h1439, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1441 | h1441
                · linarith only [h1425, h1441, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1443 | h1443
                  · linarith only [h1431, h1443, h4, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1445 | h1445
                    · linarith only [h0, h1, h1423, h1427, h1428, h1445, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1447 | h1447
                      · linarith only [h0, h1425, h1428, h1445, h1447, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                      · linarith only [h1447, h5, h6, hc45, hlam, hphi, u4ehi2]
        · linarith only [h1427, h1428, h5, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
      · linarith only [h1427, h4, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6

end R2N4
