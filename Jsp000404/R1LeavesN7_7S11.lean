import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S9
import Jsp000404.R1LeavesN7_7S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6420 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6931 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h6933 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h6935 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h6937 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 1 3 5 (by decide) (by decide) with h7656 | h7656
  · linarith only [h6418, h6937, h7656, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h7658 | h7658
    · linarith only [h2, h6420, h7658, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h7660 | h7660
      · rcases m.htr 2 3 5 (by decide) (by decide) with h7661 | h7661
        · rcases m.htr 2 4 5 (by decide) (by decide) with h7662 | h7662
          · linarith only [h6418, h6420, h6931, h6937, h7662, hc12, hc24, hlam, hphi]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h7664 | h7664
            · linarith only [h5543, h7662, h7664, hc02, hc34, hlam, hphi, ht23]
            · rcases h1bigk with h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                rcases p7666_3 (m.d 0 1) (by simp) with h7668 | h7668
                · rcases p7666_3 (m.d 1 2) (by simp) with h7669 | h7669
                  · linarith only [h7669, hlam, p7666_0]
                  · rcases p7666_3 (m.d 1 3) (by simp) with h7671 | h7671
                    · linarith only [h1, h7671, hlam]
                    · linarith only [h6931, h7671, hlam]
                · linarith only [h7668, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                rcases p7666_3 (m.d 0 1) (by simp) with h7675 | h7675
                · rcases p7666_3 (m.d 1 2) (by simp) with h7676 | h7676
                  · linarith only [h0, h7676, hlam]
                  · rcases p7666_3 (m.d 1 3) (by simp) with h7678 | h7678
                    · linarith only [h7678, hlam, p7666_0]
                    · rcases p7666_3 (m.d 1 4) (by simp) with h7680 | h7680
                      · linarith only [h2, h7680, hlam]
                      · linarith only [h6937, h7680, hlam]
                · linarith only [h7675, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                rcases p7666_3 (m.d 0 1) (by simp) with h7684 | h7684
                · rcases p7666_3 (m.d 1 2) (by simp) with h7685 | h7685
                  · linarith only [h0, h7685, hlam]
                  · rcases p7666_3 (m.d 1 3) (by simp) with h7687 | h7687
                    · linarith only [h1, h7687, hlam]
                    · rcases p7666_3 (m.d 1 4) (by simp) with h7689 | h7689
                      · linarith only [h7689, hlam, p7666_0]
                      · rcases p7666_3 (m.d 1 5) (by simp) with h7691 | h7691
                        · linarith only [h3, h7691, hlam]
                        · linarith only [h7658, h7691, hlam]
                · linarith only [h7684, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                rcases p7666_3 (m.d 0 1) (by simp) with h7695 | h7695
                · rcases p7666_3 (m.d 1 2) (by simp) with h7696 | h7696
                  · linarith only [h0, h7696, hlam]
                  · rcases p7666_3 (m.d 1 3) (by simp) with h7698 | h7698
                    · linarith only [h1, h7698, hlam]
                    · rcases p7666_3 (m.d 1 4) (by simp) with h7700 | h7700
                      · linarith only [h2, h7700, hlam]
                      · rcases p7666_3 (m.d 1 5) (by simp) with h7702 | h7702
                        · linarith only [h7702, hlam, p7666_0]
                        · rcases h1emax with h7704 | h7704 | h7704 | h7704 | h7704
                          · linarith only [h7704, hlam, hphi, ht01, ht0b, ht5b, p7666_1, u5ehi1]
                          · rcases h3bigk with h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              rcases p7706_3 (m.d 0 3) (by simp) with h7708 | h7708
                              · rcases p7706_3 (m.d 1 3) (by simp) with h7709 | h7709
                                · linarith only [h1, h7709, hlam]
                                · rcases p7706_3 (m.d 2 3) (by simp) with h7711 | h7711
                                  · rcases p7706_3 (m.d 3 4) (by simp) with h7712 | h7712
                                    · linarith only [h6418, h7712, hlam]
                                    · linarith only [h6937, h7712, hlam]
                                  · linarith only [h6931, h7711, hlam]
                              · linarith only [h1, h7708, hlam]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h4, hlam, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h4, h6931, h6937, hc12, hc23, hlam, hphi, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h4, h6931, h7656, hc12, hc23, hlam, hphi, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h1, hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h6931, hlam, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h6937, hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h7656, hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h6418, h6931, h6937, hc12, hc23, hlam, hphi, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              rcases p7706_3 (m.d 0 3) (by simp) with h7726 | h7726
                              · linarith only [h4, h7726, hlam]
                              · linarith only [h1, h7726, hlam]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h6931, h6937, hc12, hc23, hlam, hphi, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h6931, h6937, h7664, hc12, hc23, hlam, hphi, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h6418, hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h4, h6418, h6931, hc12, hc23, hlam, hphi, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h7660, hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h7664, hlam, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h6419, hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h4, h6419, h6931, hc12, hc23, hlam, hphi, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h7661, hlam, p7706_0]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [h4, h6419, h6931, h6937, hc12, hc23, hlam, hphi, p7706_1]
                            · have p7706_0 := h7706c.1
                              have p7706_1 := h7706c.2.1
                              have p7706_2 := h7706c.2.2.1
                              have p7706_3 := h7706c.2.2.2
                              linarith only [hlam, p7706_0]
                          · rcases h3bigk with h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              rcases p7742_3 (m.d 0 3) (by simp) with h7744 | h7744
                              · rcases p7742_3 (m.d 1 3) (by simp) with h7745 | h7745
                                · linarith only [h1, h7745, hlam]
                                · rcases p7742_3 (m.d 2 3) (by simp) with h7747 | h7747
                                  · rcases p7742_3 (m.d 3 4) (by simp) with h7748 | h7748
                                    · linarith only [h6418, h7748, hlam]
                                    · linarith only [h6937, h7748, hlam]
                                  · linarith only [h6931, h7747, hlam]
                              · linarith only [h1, h7744, hlam]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h4, hlam, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h4, h6931, h6937, hc12, hc23, hlam, hphi, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h4, h6931, h7656, hc12, hc23, hlam, hphi, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h1, hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h6931, hlam, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h6937, hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h7656, hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h6418, h6931, h6937, hc12, hc23, hlam, hphi, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              rcases p7742_3 (m.d 0 3) (by simp) with h7762 | h7762
                              · linarith only [h4, h7762, hlam]
                              · linarith only [h1, h7762, hlam]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h6931, h6937, hc12, hc23, hlam, hphi, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h6931, h6937, h7664, hc12, hc23, hlam, hphi, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h6418, hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h4, h6419, h6931, h7664, hc12, hc23, hlam, hphi, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h7660, hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h7664, hlam, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h6419, hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h4, h6419, h6931, hc12, hc23, hlam, hphi, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h7661, hlam, p7742_0]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [h4, h6419, h6931, h6937, hc12, hc23, hlam, hphi, p7742_1]
                            · have p7742_0 := h7742c.1
                              have p7742_1 := h7742c.2.1
                              have p7742_2 := h7742c.2.2.1
                              have p7742_3 := h7742c.2.2.2
                              linarith only [hlam, p7742_0]
                          · rcases h3bigk with h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              rcases p7778_3 (m.d 0 3) (by simp) with h7780 | h7780
                              · rcases p7778_3 (m.d 1 3) (by simp) with h7781 | h7781
                                · linarith only [h1, h7781, hlam]
                                · rcases p7778_3 (m.d 2 3) (by simp) with h7783 | h7783
                                  · rcases p7778_3 (m.d 3 4) (by simp) with h7784 | h7784
                                    · linarith only [h6418, h7784, hlam]
                                    · linarith only [h6937, h7784, hlam]
                                  · linarith only [h6931, h7783, hlam]
                              · linarith only [h1, h7780, hlam]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h4, hlam, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h4, h6931, h6937, hc12, hc23, hlam, hphi, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h4, h6931, h7656, hc12, hc23, hlam, hphi, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h1, hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h6931, hlam, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h6937, hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h7656, hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h6418, h6931, h6937, hc12, hc23, hlam, hphi, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              rcases p7778_3 (m.d 0 3) (by simp) with h7798 | h7798
                              · linarith only [h4, h7798, hlam]
                              · linarith only [h1, h7798, hlam]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h6931, h6937, hc12, hc23, hlam, hphi, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h6931, h6937, h7664, hc12, hc23, hlam, hphi, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h6418, hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h4, h6419, h6931, h7664, hc12, hc23, hlam, hphi, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h7660, hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h7664, hlam, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h6419, hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h4, h6419, h6931, hc12, hc23, hlam, hphi, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h7661, hlam, p7778_0]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [h4, h6419, h6931, h6937, hc12, hc23, hlam, hphi, p7778_1]
                            · have p7778_0 := h7778c.1
                              have p7778_1 := h7778c.2.1
                              have p7778_2 := h7778c.2.2.1
                              have p7778_3 := h7778c.2.2.2
                              linarith only [hlam, p7778_0]
                          · rcases h3bigk with h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              rcases p7814_3 (m.d 0 3) (by simp) with h7816 | h7816
                              · rcases p7814_3 (m.d 1 3) (by simp) with h7817 | h7817
                                · linarith only [h1, h7817, hlam]
                                · rcases p7814_3 (m.d 2 3) (by simp) with h7819 | h7819
                                  · rcases p7814_3 (m.d 3 4) (by simp) with h7820 | h7820
                                    · linarith only [h6418, h7820, hlam]
                                    · linarith only [h6937, h7820, hlam]
                                  · linarith only [h6931, h7819, hlam]
                              · linarith only [h1, h7816, hlam]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h4, hlam, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h4, h6931, h6937, hc12, hc23, hlam, hphi, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h4, h6931, h7656, hc12, hc23, hlam, hphi, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h1, hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h6931, hlam, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h6937, hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h7656, hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h6418, h6931, h6937, hc12, hc23, hlam, hphi, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              rcases p7814_3 (m.d 0 3) (by simp) with h7834 | h7834
                              · linarith only [h4, h7834, hlam]
                              · linarith only [h1, h7834, hlam]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h6931, h6937, hc12, hc23, hlam, hphi, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h6931, h6937, h7664, hc12, hc23, hlam, hphi, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h6418, hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h4, h6418, h6931, hc12, hc23, hlam, hphi, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h7660, hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h7664, hlam, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h6419, hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h4, h6419, h6931, hc12, hc23, hlam, hphi, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h7661, hlam, p7814_0]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [h4, h6419, h6931, h6937, hc12, hc23, hlam, hphi, p7814_1]
                            · have p7814_0 := h7814c.1
                              have p7814_1 := h7814c.2.1
                              have p7814_2 := h7814c.2.2.1
                              have p7814_3 := h7814c.2.2.2
                              linarith only [hlam, p7814_0]
                · linarith only [h7695, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h0, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h6931, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h6933, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h6935, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h1, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h2, h5543, h6937, h7662, hc12, hc45, hlam, hphi, ht23, ht34, p7666_1]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h6937, hlam, p7666_1]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h7656, hlam, p7666_1]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h2, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h2, h5543, h7662, hc12, hc45, hlam, hphi, ht23, ht34, p7666_1]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h2, h5543, h7662, hc13, hc45, hlam, hphi, ht34, p7666_1]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h7658, hlam, p7666_1]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h3, hlam, p7666_0]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h4, h6419, h7656, hc12, hc23, hlam, hphi, p7666_1]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h4, h6419, h6931, h7656, hc12, hc23, hlam, hphi, p7666_1]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [h4, h6419, h6933, h7656, hc12, hc23, hlam, hphi, p7666_1]
              · have p7666_0 := h7666c.1
                have p7666_1 := h7666c.2.1
                have p7666_2 := h7666c.2.2.1
                have p7666_3 := h7666c.2.2.2
                linarith only [hlam, p7666_0]
        · linarith only [h4, h6419, h7661, hlam]
      · linarith only [h4, h6418, h7660, hlam]

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6420 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6931 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h6933 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h6935 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 1 3 4 (by decide) (by decide) with h6937 | h6937
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419 h6420 h6931 h6933 h6935 h6937
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419 h6420 h6931 h6933 h6935 h6937

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6420 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6931 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h6933 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 1 2 5 (by decide) (by decide) with h6935 | h6935
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419 h6420 h6931 h6933 h6935
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419 h6420 h6931 h6933 h6935

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6420 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6931 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 1 2 4 (by decide) (by decide) with h6933 | h6933
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419 h6420 h6931 h6933
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419 h6420 h6931 h6933

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6420 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 1 2 3 (by decide) (by decide) with h6931 | h6931
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419 h6420 h6931
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419 h6420 h6931

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 0 4 5 (by decide) (by decide) with h6420 | h6420
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419 h6420
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h6419 h6420

end R2N4
