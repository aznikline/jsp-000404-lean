import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S50

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x1_x0_x1 (m : N7Model)
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
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h30180 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h30182 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h30184 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h30186 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h30188 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h30189 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h30667 | h30667
  · linarith only [h1, h29475, h30178, h30189, h30667, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h30669 | h30669
    · rcases m.htr 3 4 5 (by decide) (by decide) with h30670 | h30670
      · rcases h1bigk with h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c | h30671c
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          rcases p30671_3 (m.d 0 1) (by simp) with h30673 | h30673
          · rcases p30671_3 (m.d 1 2) (by simp) with h30674 | h30674
            · linarith only [h30674, hlam, p30671_0]
            · rcases p30671_3 (m.d 1 3) (by simp) with h30676 | h30676
              · linarith only [h1, h30676, hlam]
              · linarith only [h30178, h30676, hlam]
          · linarith only [h30673, hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          rcases p30671_3 (m.d 0 1) (by simp) with h30680 | h30680
          · rcases p30671_3 (m.d 1 2) (by simp) with h30681 | h30681
            · linarith only [h0, h30681, hlam]
            · rcases p30671_3 (m.d 1 3) (by simp) with h30683 | h30683
              · linarith only [h30683, hlam, p30671_0]
              · rcases p30671_3 (m.d 1 4) (by simp) with h30685 | h30685
                · linarith only [h2, h30685, hlam]
                · linarith only [h30184, h30685, hlam]
          · linarith only [h30680, hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          rcases p30671_3 (m.d 0 1) (by simp) with h30689 | h30689
          · rcases p30671_3 (m.d 1 2) (by simp) with h30690 | h30690
            · linarith only [h0, h30690, hlam]
            · rcases p30671_3 (m.d 1 3) (by simp) with h30692 | h30692
              · linarith only [h1, h30692, hlam]
              · rcases p30671_3 (m.d 1 4) (by simp) with h30694 | h30694
                · linarith only [h30694, hlam, p30671_0]
                · rcases p30671_3 (m.d 1 5) (by simp) with h30696 | h30696
                  · linarith only [h3, h30696, hlam]
                  · rcases h1emax with h30698 | h30698 | h30698 | h30698 | h30698
                    · linarith only [h30188, h30698, hc45, hlam, hphi, ht01, ht0b, ht5b, p30671_1]
                    · rcases h2bigk with h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c | h30700c
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [hlam, p30700_0]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h30667, h30670, h4, hc12, hc34, hlam, hphi, ht23, p30700_1]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h4, hlam, p30700_0]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h19744, hlam, p30700_0]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h22010, hlam, p30700_0]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h0, hlam, p30700_1]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [hlam, p30700_0]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h30178, hlam, p30700_0]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h30180, hlam, p30700_0]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h30182, hlam, p30700_0]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h30667, h30670, hc02, hc34, hlam, hphi, ht23, p30700_1]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h30667, h30670, hc12, hc34, hlam, hphi, ht23, p30700_1]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [hlam, p30700_0]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h30189, hlam, p30700_1]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h30667, hlam, p30700_1]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        rcases p30700_3 (m.d 0 2) (by simp) with h30716 | h30716
                        · linarith only [h30716, hlam, p30700_0]
                        · rcases p30700_3 (m.d 1 2) (by simp) with h30718 | h30718
                          · linarith only [h30180, h30718, hlam]
                          · rcases p30700_3 (m.d 2 3) (by simp) with h30720 | h30720
                            · linarith only [h30189, h30720, hlam]
                            · linarith only [h30720, h4, hlam]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        rcases p30700_3 (m.d 0 2) (by simp) with h30723 | h30723
                        · linarith only [h19744, h30723, hlam]
                        · linarith only [h0, h30723, hlam]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h0, h4, hc12, hc24, hlam, hphi, p30700_1]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [hlam, p30700_0]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h0, h30189, h30667, h4, hc12, hc34, hlam, hphi, ht23, p30700_1]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        rcases p30700_3 (m.d 0 2) (by simp) with h30729 | h30729
                        · linarith only [h30729, hlam, p30700_0]
                        · rcases p30700_3 (m.d 1 2) (by simp) with h30731 | h30731
                          · linarith only [h30182, h30731, hlam]
                          · rcases p30700_3 (m.d 2 3) (by simp) with h30733 | h30733
                            · linarith only [h30667, h30733, hlam]
                            · linarith only [h30733, h4, hlam]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        rcases p30700_3 (m.d 0 2) (by simp) with h30736 | h30736
                        · linarith only [h22010, h30736, hlam]
                        · linarith only [h0, h30736, hlam]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p30700_1]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [h30669, hlam, p30700_1]
                      · have p30700_0 := h30700c.1
                        have p30700_1 := h30700c.2.1
                        have p30700_2 := h30700c.2.2.1
                        have p30700_3 := h30700c.2.2.2
                        linarith only [hlam, p30700_0]
                    · rcases h2bigk with h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c | h30742c
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [hlam, p30742_0]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p30742_1]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h4, hlam, p30742_0]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h19744, hlam, p30742_0]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h22010, hlam, p30742_0]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h0, hlam, p30742_1]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [hlam, p30742_0]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h30178, hlam, p30742_0]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h30180, hlam, p30742_0]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h30182, hlam, p30742_0]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h30189, hc02, hc34, hlam, hphi, ht23, p30742_1]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h30189, hc12, hc34, hlam, hphi, ht23, p30742_1]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [hlam, p30742_0]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h30189, hlam, p30742_1]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h30667, hlam, p30742_1]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        rcases p30742_3 (m.d 0 2) (by simp) with h30758 | h30758
                        · linarith only [h30758, hlam, p30742_0]
                        · rcases p30742_3 (m.d 1 2) (by simp) with h30760 | h30760
                          · linarith only [h30180, h30760, hlam]
                          · rcases p30742_3 (m.d 2 3) (by simp) with h30762 | h30762
                            · linarith only [h30189, h30762, hlam]
                            · linarith only [h30762, h4, hlam]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        rcases p30742_3 (m.d 0 2) (by simp) with h30765 | h30765
                        · linarith only [h19744, h30765, hlam]
                        · linarith only [h0, h30765, hlam]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h0, h30189, h4, hc12, hc34, hlam, hphi, ht23, p30742_1]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [hlam, p30742_0]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h0, h22010, h30189, hc12, hc34, hlam, hphi, ht23, p30742_1]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        rcases p30742_3 (m.d 0 2) (by simp) with h30771 | h30771
                        · linarith only [h30771, hlam, p30742_0]
                        · rcases p30742_3 (m.d 1 2) (by simp) with h30773 | h30773
                          · linarith only [h30182, h30773, hlam]
                          · rcases p30742_3 (m.d 2 3) (by simp) with h30775 | h30775
                            · linarith only [h30667, h30775, hlam]
                            · linarith only [h30775, h4, hlam]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        rcases p30742_3 (m.d 0 2) (by simp) with h30778 | h30778
                        · linarith only [h22010, h30778, hlam]
                        · linarith only [h0, h30778, hlam]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p30742_1]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [h30669, hlam, p30742_1]
                      · have p30742_0 := h30742c.1
                        have p30742_1 := h30742c.2.1
                        have p30742_2 := h30742c.2.2.1
                        have p30742_3 := h30742c.2.2.2
                        linarith only [hlam, p30742_0]
                    · rcases h2bigk with h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c | h30784c
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [hlam, p30784_0]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p30784_1]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h4, hlam, p30784_0]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h19744, hlam, p30784_0]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h22010, hlam, p30784_0]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h0, hlam, p30784_1]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [hlam, p30784_0]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h30178, hlam, p30784_0]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h30180, hlam, p30784_0]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h30182, hlam, p30784_0]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h30189, hc02, hc34, hlam, hphi, ht23, p30784_1]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h30189, hc12, hc34, hlam, hphi, ht23, p30784_1]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [hlam, p30784_0]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h30189, hlam, p30784_1]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h30667, hlam, p30784_1]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        rcases p30784_3 (m.d 0 2) (by simp) with h30800 | h30800
                        · linarith only [h30800, hlam, p30784_0]
                        · rcases p30784_3 (m.d 1 2) (by simp) with h30802 | h30802
                          · linarith only [h30180, h30802, hlam]
                          · rcases p30784_3 (m.d 2 3) (by simp) with h30804 | h30804
                            · linarith only [h30189, h30804, hlam]
                            · linarith only [h30804, h4, hlam]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        rcases p30784_3 (m.d 0 2) (by simp) with h30807 | h30807
                        · linarith only [h19744, h30807, hlam]
                        · linarith only [h0, h30807, hlam]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h0, h30189, h4, hc12, hc34, hlam, hphi, ht23, p30784_1]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [hlam, p30784_0]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h0, h22010, h30189, hc12, hc34, hlam, hphi, ht23, p30784_1]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        rcases p30784_3 (m.d 0 2) (by simp) with h30813 | h30813
                        · linarith only [h30813, hlam, p30784_0]
                        · rcases p30784_3 (m.d 1 2) (by simp) with h30815 | h30815
                          · linarith only [h30182, h30815, hlam]
                          · rcases p30784_3 (m.d 2 3) (by simp) with h30817 | h30817
                            · linarith only [h30667, h30817, hlam]
                            · linarith only [h30817, h4, hlam]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        rcases p30784_3 (m.d 0 2) (by simp) with h30820 | h30820
                        · linarith only [h22010, h30820, hlam]
                        · linarith only [h0, h30820, hlam]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p30784_1]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [h30669, hlam, p30784_1]
                      · have p30784_0 := h30784c.1
                        have p30784_1 := h30784c.2.1
                        have p30784_2 := h30784c.2.2.1
                        have p30784_3 := h30784c.2.2.2
                        linarith only [hlam, p30784_0]
                    · rcases h2bigk with h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c | h30826c
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [hlam, p30826_0]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p30826_1]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h4, hlam, p30826_0]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h19744, hlam, p30826_0]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h22010, hlam, p30826_0]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h0, hlam, p30826_1]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [hlam, p30826_0]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h30178, hlam, p30826_0]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h30180, hlam, p30826_0]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h30182, hlam, p30826_0]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h30189, hc02, hc34, hlam, hphi, ht23, p30826_1]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h30189, hc12, hc34, hlam, hphi, ht23, p30826_1]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [hlam, p30826_0]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h30189, hlam, p30826_1]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h30667, hlam, p30826_1]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        rcases p30826_3 (m.d 0 2) (by simp) with h30842 | h30842
                        · linarith only [h30842, hlam, p30826_0]
                        · rcases p30826_3 (m.d 1 2) (by simp) with h30844 | h30844
                          · linarith only [h30180, h30844, hlam]
                          · rcases p30826_3 (m.d 2 3) (by simp) with h30846 | h30846
                            · linarith only [h30189, h30846, hlam]
                            · linarith only [h30846, h4, hlam]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        rcases p30826_3 (m.d 0 2) (by simp) with h30849 | h30849
                        · linarith only [h19744, h30849, hlam]
                        · linarith only [h0, h30849, hlam]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h0, h30189, h4, hc12, hc34, hlam, hphi, ht23, p30826_1]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [hlam, p30826_0]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h0, h22010, h30189, hc12, hc34, hlam, hphi, ht23, p30826_1]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        rcases p30826_3 (m.d 0 2) (by simp) with h30855 | h30855
                        · linarith only [h30855, hlam, p30826_0]
                        · rcases p30826_3 (m.d 1 2) (by simp) with h30857 | h30857
                          · linarith only [h30182, h30857, hlam]
                          · rcases p30826_3 (m.d 2 3) (by simp) with h30859 | h30859
                            · linarith only [h30667, h30859, hlam]
                            · linarith only [h30859, h4, hlam]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        rcases p30826_3 (m.d 0 2) (by simp) with h30862 | h30862
                        · linarith only [h22010, h30862, hlam]
                        · linarith only [h0, h30862, hlam]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p30826_1]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [h30669, hlam, p30826_1]
                      · have p30826_0 := h30826c.1
                        have p30826_1 := h30826c.2.1
                        have p30826_2 := h30826c.2.2.1
                        have p30826_3 := h30826c.2.2.2
                        linarith only [hlam, p30826_0]
          · linarith only [h30689, hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          rcases p30671_3 (m.d 0 1) (by simp) with h30869 | h30869
          · rcases p30671_3 (m.d 1 2) (by simp) with h30870 | h30870
            · linarith only [h0, h30870, hlam]
            · rcases p30671_3 (m.d 1 3) (by simp) with h30872 | h30872
              · linarith only [h1, h30872, hlam]
              · rcases p30671_3 (m.d 1 4) (by simp) with h30874 | h30874
                · linarith only [h2, h30874, hlam]
                · linarith only [h30188, h30874, hlam]
          · linarith only [h30869, hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h0, hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h30178, hlam, p30671_1]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h30180, hlam, p30671_1]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h30182, hlam, p30671_1]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h1, hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h1, h23337, hc12, hc34, hlam, hphi, ht23, p30671_1]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h30184, hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h30186, hlam, p30671_1]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h2, hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          rcases p30671_3 (m.d 0 1) (by simp) with h30889 | h30889
          · rcases p30671_3 (m.d 1 2) (by simp) with h30890 | h30890
            · linarith only [h30180, h30890, hlam]
            · rcases p30671_3 (m.d 1 3) (by simp) with h30892 | h30892
              · linarith only [h30184, h30892, hlam]
              · linarith only [h30178, h30892, hlam]
          · linarith only [h0, h30889, hlam]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          rcases p30671_3 (m.d 0 1) (by simp) with h30896 | h30896
          · rcases p30671_3 (m.d 1 2) (by simp) with h30897 | h30897
            · linarith only [h30180, h30897, hlam]
            · rcases p30671_3 (m.d 1 3) (by simp) with h30899 | h30899
              · linarith only [h30184, h30899, hlam]
              · rcases p30671_3 (m.d 1 4) (by simp) with h30901 | h30901
                · rcases p30671_3 (m.d 1 5) (by simp) with h30902 | h30902
                  · linarith only [h30188, h30902, hlam]
                  · linarith only [h30186, h30902, hlam]
                · linarith only [h30184, h30901, hlam]
          · linarith only [h1, h30896, hlam]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          rcases p30671_3 (m.d 0 1) (by simp) with h30908 | h30908
          · rcases p30671_3 (m.d 1 2) (by simp) with h30909 | h30909
            · linarith only [h30180, h30909, hlam]
            · rcases p30671_3 (m.d 1 3) (by simp) with h30911 | h30911
              · linarith only [h30184, h30911, hlam]
              · rcases p30671_3 (m.d 1 4) (by simp) with h30913 | h30913
                · rcases p30671_3 (m.d 1 5) (by simp) with h30914 | h30914
                  · linarith only [h30188, h30914, hlam]
                  · rcases h1emax with h30916 | h30916 | h30916 | h30916 | h30916
                    · linarith only [h2, h30178, h30186, h30916, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p30671_1]
                    · rcases h2bigk with h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c | h30918c
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [hlam, p30918_0]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h30667, h30670, h4, hc12, hc34, hlam, hphi, ht23, p30918_1]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h4, hlam, p30918_0]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h19744, hlam, p30918_0]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h22010, hlam, p30918_0]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h0, hlam, p30918_1]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [hlam, p30918_0]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h30178, hlam, p30918_0]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h30180, hlam, p30918_0]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h30182, hlam, p30918_0]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h30667, h30670, hc02, hc34, hlam, hphi, ht23, p30918_1]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h30667, h30670, hc12, hc34, hlam, hphi, ht23, p30918_1]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [hlam, p30918_0]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h30189, hlam, p30918_1]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h30667, hlam, p30918_1]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        rcases p30918_3 (m.d 0 2) (by simp) with h30934 | h30934
                        · linarith only [h30934, hlam, p30918_0]
                        · rcases p30918_3 (m.d 1 2) (by simp) with h30936 | h30936
                          · linarith only [h30180, h30936, hlam]
                          · rcases p30918_3 (m.d 2 3) (by simp) with h30938 | h30938
                            · linarith only [h30189, h30938, hlam]
                            · linarith only [h30938, h4, hlam]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        rcases p30918_3 (m.d 0 2) (by simp) with h30941 | h30941
                        · linarith only [h19744, h30941, hlam]
                        · linarith only [h0, h30941, hlam]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h0, h30189, h4, hc12, hc34, hlam, hphi, ht23, p30918_1]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [hlam, p30918_0]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h0, h22010, h30189, hc12, hc34, hlam, hphi, ht23, p30918_1]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        rcases p30918_3 (m.d 0 2) (by simp) with h30947 | h30947
                        · linarith only [h30947, hlam, p30918_0]
                        · rcases p30918_3 (m.d 1 2) (by simp) with h30949 | h30949
                          · linarith only [h30182, h30949, hlam]
                          · rcases p30918_3 (m.d 2 3) (by simp) with h30951 | h30951
                            · linarith only [h30667, h30951, hlam]
                            · linarith only [h30951, h4, hlam]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        rcases p30918_3 (m.d 0 2) (by simp) with h30954 | h30954
                        · linarith only [h22010, h30954, hlam]
                        · linarith only [h0, h30954, hlam]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p30918_1]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [h30669, hlam, p30918_1]
                      · have p30918_0 := h30918c.1
                        have p30918_1 := h30918c.2.1
                        have p30918_2 := h30918c.2.2.1
                        have p30918_3 := h30918c.2.2.2
                        linarith only [hlam, p30918_0]
                    · rcases h2bigk with h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c | h30960c
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [hlam, p30960_0]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p30960_1]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h4, hlam, p30960_0]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h19744, hlam, p30960_0]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h22010, hlam, p30960_0]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h0, hlam, p30960_1]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [hlam, p30960_0]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h30178, hlam, p30960_0]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h30180, hlam, p30960_0]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h30182, hlam, p30960_0]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h30189, hc02, hc34, hlam, hphi, ht23, p30960_1]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h30189, hc12, hc34, hlam, hphi, ht23, p30960_1]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [hlam, p30960_0]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h30189, hlam, p30960_1]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h30667, hlam, p30960_1]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        rcases p30960_3 (m.d 0 2) (by simp) with h30976 | h30976
                        · linarith only [h30976, hlam, p30960_0]
                        · rcases p30960_3 (m.d 1 2) (by simp) with h30978 | h30978
                          · linarith only [h30180, h30978, hlam]
                          · rcases p30960_3 (m.d 2 3) (by simp) with h30980 | h30980
                            · linarith only [h30189, h30980, hlam]
                            · linarith only [h30980, h4, hlam]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        rcases p30960_3 (m.d 0 2) (by simp) with h30983 | h30983
                        · linarith only [h19744, h30983, hlam]
                        · linarith only [h0, h30983, hlam]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h0, h30189, h4, hc12, hc34, hlam, hphi, ht23, p30960_1]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [hlam, p30960_0]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h0, h22010, h30189, hc12, hc34, hlam, hphi, ht23, p30960_1]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        rcases p30960_3 (m.d 0 2) (by simp) with h30989 | h30989
                        · linarith only [h30989, hlam, p30960_0]
                        · rcases p30960_3 (m.d 1 2) (by simp) with h30991 | h30991
                          · linarith only [h30182, h30991, hlam]
                          · rcases p30960_3 (m.d 2 3) (by simp) with h30993 | h30993
                            · linarith only [h30667, h30993, hlam]
                            · linarith only [h30993, h4, hlam]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        rcases p30960_3 (m.d 0 2) (by simp) with h30996 | h30996
                        · linarith only [h22010, h30996, hlam]
                        · linarith only [h0, h30996, hlam]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p30960_1]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [h30669, hlam, p30960_1]
                      · have p30960_0 := h30960c.1
                        have p30960_1 := h30960c.2.1
                        have p30960_2 := h30960c.2.2.1
                        have p30960_3 := h30960c.2.2.2
                        linarith only [hlam, p30960_0]
                    · linarith only [h30178, h30186, h30916, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p30671_1]
                    · rcases h2bigk with h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c | h31003c
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [hlam, p31003_0]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p31003_1]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h4, hlam, p31003_0]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h19744, hlam, p31003_0]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h22010, hlam, p31003_0]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h0, hlam, p31003_1]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [hlam, p31003_0]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h30178, hlam, p31003_0]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h30180, hlam, p31003_0]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h30182, hlam, p31003_0]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h30189, hc02, hc34, hlam, hphi, ht23, p31003_1]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h30189, hc12, hc34, hlam, hphi, ht23, p31003_1]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [hlam, p31003_0]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h30189, hlam, p31003_1]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h30667, hlam, p31003_1]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        rcases p31003_3 (m.d 0 2) (by simp) with h31019 | h31019
                        · linarith only [h31019, hlam, p31003_0]
                        · rcases p31003_3 (m.d 1 2) (by simp) with h31021 | h31021
                          · linarith only [h30180, h31021, hlam]
                          · rcases p31003_3 (m.d 2 3) (by simp) with h31023 | h31023
                            · linarith only [h30189, h31023, hlam]
                            · linarith only [h31023, h4, hlam]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        rcases p31003_3 (m.d 0 2) (by simp) with h31026 | h31026
                        · linarith only [h19744, h31026, hlam]
                        · linarith only [h0, h31026, hlam]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h0, h30189, h4, hc12, hc34, hlam, hphi, ht23, p31003_1]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [hlam, p31003_0]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h0, h22010, h30189, hc12, hc34, hlam, hphi, ht23, p31003_1]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        rcases p31003_3 (m.d 0 2) (by simp) with h31032 | h31032
                        · linarith only [h31032, hlam, p31003_0]
                        · rcases p31003_3 (m.d 1 2) (by simp) with h31034 | h31034
                          · linarith only [h30182, h31034, hlam]
                          · rcases p31003_3 (m.d 2 3) (by simp) with h31036 | h31036
                            · linarith only [h30667, h31036, hlam]
                            · linarith only [h31036, h4, hlam]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        rcases p31003_3 (m.d 0 2) (by simp) with h31039 | h31039
                        · linarith only [h22010, h31039, hlam]
                        · linarith only [h0, h31039, hlam]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p31003_1]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [h30669, hlam, p31003_1]
                      · have p31003_0 := h31003c.1
                        have p31003_1 := h31003c.2.1
                        have p31003_2 := h31003c.2.2.1
                        have p31003_3 := h31003c.2.2.2
                        linarith only [hlam, p31003_0]
                · linarith only [h30188, h30913, hlam]
          · linarith only [h3, h30908, hlam]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h3, hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          rcases p30671_3 (m.d 0 1) (by simp) with h31048 | h31048
          · rcases p30671_3 (m.d 1 2) (by simp) with h31049 | h31049
            · linarith only [h30182, h31049, hlam]
            · rcases p30671_3 (m.d 1 3) (by simp) with h31051 | h31051
              · linarith only [h30186, h31051, hlam]
              · linarith only [h30178, h31051, hlam]
          · linarith only [h0, h31048, hlam]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          rcases p30671_3 (m.d 0 1) (by simp) with h31055 | h31055
          · rcases p30671_3 (m.d 1 2) (by simp) with h31056 | h31056
            · linarith only [h30182, h31056, hlam]
            · rcases p30671_3 (m.d 1 3) (by simp) with h31058 | h31058
              · linarith only [h30186, h31058, hlam]
              · rcases p30671_3 (m.d 1 4) (by simp) with h31060 | h31060
                · rcases p30671_3 (m.d 1 5) (by simp) with h31061 | h31061
                  · rcases h1emax with h31062 | h31062 | h31062 | h31062 | h31062
                    · linarith only [h3, h30178, h31062, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p30671_1]
                    · rcases h2bigk with h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c | h31064c
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [hlam, p31064_0]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p31064_1]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h4, hlam, p31064_0]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h19744, hlam, p31064_0]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h22010, hlam, p31064_0]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h0, hlam, p31064_1]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [hlam, p31064_0]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h30178, hlam, p31064_0]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h30180, hlam, p31064_0]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h30182, hlam, p31064_0]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h30189, hc02, hc34, hlam, hphi, ht23, p31064_1]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h30189, hc12, hc34, hlam, hphi, ht23, p31064_1]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [hlam, p31064_0]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h30189, hlam, p31064_1]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h30667, hlam, p31064_1]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        rcases p31064_3 (m.d 0 2) (by simp) with h31080 | h31080
                        · linarith only [h31080, hlam, p31064_0]
                        · rcases p31064_3 (m.d 1 2) (by simp) with h31082 | h31082
                          · linarith only [h30180, h31082, hlam]
                          · rcases p31064_3 (m.d 2 3) (by simp) with h31084 | h31084
                            · linarith only [h30189, h31084, hlam]
                            · linarith only [h31084, h4, hlam]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        rcases p31064_3 (m.d 0 2) (by simp) with h31087 | h31087
                        · linarith only [h19744, h31087, hlam]
                        · linarith only [h0, h31087, hlam]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h0, h30189, h4, hc12, hc34, hlam, hphi, ht23, p31064_1]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [hlam, p31064_0]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h0, h22010, h30189, hc12, hc34, hlam, hphi, ht23, p31064_1]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        rcases p31064_3 (m.d 0 2) (by simp) with h31093 | h31093
                        · linarith only [h31093, hlam, p31064_0]
                        · rcases p31064_3 (m.d 1 2) (by simp) with h31095 | h31095
                          · linarith only [h30182, h31095, hlam]
                          · rcases p31064_3 (m.d 2 3) (by simp) with h31097 | h31097
                            · linarith only [h30667, h31097, hlam]
                            · linarith only [h31097, h4, hlam]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        rcases p31064_3 (m.d 0 2) (by simp) with h31100 | h31100
                        · linarith only [h22010, h31100, hlam]
                        · linarith only [h0, h31100, hlam]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p31064_1]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [h30669, hlam, p31064_1]
                      · have p31064_0 := h31064c.1
                        have p31064_1 := h31064c.2.1
                        have p31064_2 := h31064c.2.2.1
                        have p31064_3 := h31064c.2.2.2
                        linarith only [hlam, p31064_0]
                    · rcases h2bigk with h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c | h31106c
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [hlam, p31106_0]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p31106_1]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h4, hlam, p31106_0]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h19744, hlam, p31106_0]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h22010, hlam, p31106_0]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h0, hlam, p31106_1]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [hlam, p31106_0]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h30178, hlam, p31106_0]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h30180, hlam, p31106_0]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h30182, hlam, p31106_0]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h30189, hc02, hc34, hlam, hphi, ht23, p31106_1]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h30189, hc12, hc34, hlam, hphi, ht23, p31106_1]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [hlam, p31106_0]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h30189, hlam, p31106_1]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h30667, hlam, p31106_1]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        rcases p31106_3 (m.d 0 2) (by simp) with h31122 | h31122
                        · linarith only [h31122, hlam, p31106_0]
                        · rcases p31106_3 (m.d 1 2) (by simp) with h31124 | h31124
                          · linarith only [h30180, h31124, hlam]
                          · rcases p31106_3 (m.d 2 3) (by simp) with h31126 | h31126
                            · linarith only [h30189, h31126, hlam]
                            · linarith only [h31126, h4, hlam]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        rcases p31106_3 (m.d 0 2) (by simp) with h31129 | h31129
                        · linarith only [h19744, h31129, hlam]
                        · linarith only [h0, h31129, hlam]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h0, h30189, h4, hc12, hc34, hlam, hphi, ht23, p31106_1]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [hlam, p31106_0]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h0, h22010, h30189, hc12, hc34, hlam, hphi, ht23, p31106_1]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        rcases p31106_3 (m.d 0 2) (by simp) with h31135 | h31135
                        · linarith only [h31135, hlam, p31106_0]
                        · rcases p31106_3 (m.d 1 2) (by simp) with h31137 | h31137
                          · linarith only [h30182, h31137, hlam]
                          · rcases p31106_3 (m.d 2 3) (by simp) with h31139 | h31139
                            · linarith only [h30667, h31139, hlam]
                            · linarith only [h31139, h4, hlam]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        rcases p31106_3 (m.d 0 2) (by simp) with h31142 | h31142
                        · linarith only [h22010, h31142, hlam]
                        · linarith only [h0, h31142, hlam]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p31106_1]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [h30669, hlam, p31106_1]
                      · have p31106_0 := h31106c.1
                        have p31106_1 := h31106c.2.1
                        have p31106_2 := h31106c.2.2.1
                        have p31106_3 := h31106c.2.2.2
                        linarith only [hlam, p31106_0]
                    · linarith only [h30178, h30188, h31062, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p30671_1]
                    · linarith only [h30178, h31062, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p30671_1]
                  · linarith only [h30186, h31061, hlam]
                · linarith only [h30184, h31060, hlam]
          · linarith only [h1, h31055, hlam]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [h30188, hlam, p30671_0]
        · have p30671_0 := h30671c.1
          have p30671_1 := h30671c.2.1
          have p30671_2 := h30671c.2.2.1
          have p30671_3 := h30671c.2.2.2
          linarith only [hlam, p30671_0]
      · linarith only [h19744, h30177, h30189, h30670, hlam]
    · linarith only [h19744, h2, h30188, h30669, hlam]

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x1_x0 (m : N7Model)
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
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h30180 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h30182 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h30184 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h30186 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h30188 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h30189 | h30189
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180 h30182 h30184 h30186 h30188 h30189
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180 h30182 h30184 h30186 h30188 h30189

end R2N4
