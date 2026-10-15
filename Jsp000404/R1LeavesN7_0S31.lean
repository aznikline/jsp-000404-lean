import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 0 1) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 0 1) ∧ (m.d 1 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 2) ≤ z)))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  rcases p17727_3 (m.d 0 1) (by simp) with h17729 | h17729
  · rcases p17727_3 (m.d 1 2) (by simp) with h17730 | h17730
    · linarith only [h17730, hlam, p17727_0]
    · rcases p17727_3 (m.d 1 3) (by simp) with h17732 | h17732
      · linarith only [h1, h17732, hlam]
      · rcases p17727_3 (m.d 1 4) (by simp) with h17734 | h17734
        · linarith only [h17734, h2, hlam]
        · rcases p17727_3 (m.d 1 5) (by simp) with h17736 | h17736
          · linarith only [h17736, h3, hlam]
          · rcases h1emax with h17738 | h17738 | h17738 | h17738 | h17738
            · linarith only [h17738, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p17727_1]
            · rcases h2bigk with h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c | h17740c
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                rcases p17740_3 (m.d 0 2) (by simp) with h17742 | h17742
                · rcases p17740_3 (m.d 1 2) (by simp) with h17743 | h17743
                  · linarith only [h0, h17743, hlam]
                  · rcases p17740_3 (m.d 2 3) (by simp) with h17745 | h17745
                    · linarith only [h17745, h4, hlam]
                    · rcases p17740_3 (m.d 2 4) (by simp) with h17747 | h17747
                      · linarith only [h17747, h5, hlam]
                      · rcases p17740_3 (m.d 2 5) (by simp) with h17749 | h17749
                        · linarith only [h17749, h6, hlam]
                        · rcases h4bigk with h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c | h17751c
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16969, h16972, h16984, h7, hc23, hc45, hlam, hphi, ht34, p17751_1]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p17751_1]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h7, hlam, p17751_1]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h14159, hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h2, hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16978, h16984, h2, h7, hc23, hc45, hlam, hphi, ht34, p17751_1]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16972, hlam, p17751_1]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16976, hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h5, hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16970, hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16978, hlam, p17751_1]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16982, hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16984, hc04, hc45, hlam, hphi, p17751_1]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16970, h16978, h16984, hc23, hc45, hlam, hphi, ht34, p17751_1]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16978, h16984, hc23, hc45, hlam, hphi, ht34, p17751_1]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h16984, hlam, p17751_0]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            rcases p17751_3 (m.d 0 4) (by simp) with h17772 | h17772
                            · linarith only [h17772, hlam, p17751_0]
                            · rcases p17751_3 (m.d 1 4) (by simp) with h17774 | h17774
                              · linarith only [h16976, h17774, hlam]
                              · rcases p17751_3 (m.d 2 4) (by simp) with h17776 | h17776
                                · linarith only [h16982, h17776, hlam]
                                · rcases p17751_3 (m.d 3 4) (by simp) with h17778 | h17778
                                  · linarith only [h16984, h17778, hlam]
                                  · linarith only [h17778, h7, hlam]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            rcases p17751_3 (m.d 0 4) (by simp) with h17781 | h17781
                            · linarith only [h14159, h17781, hlam]
                            · linarith only [h17781, h2, hlam]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            rcases p17751_3 (m.d 0 4) (by simp) with h17784 | h17784
                            · linarith only [h14159, h17784, hlam]
                            · linarith only [h17784, h5, hlam]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [h1, h16969, h7, hc23, hc45, hlam, hphi, ht34, p17751_1]
                          · have p17751_0 := h17751c.1
                            have p17751_1 := h17751c.2.1
                            have p17751_2 := h17751c.2.2.1
                            have p17751_3 := h17751c.2.2.2
                            linarith only [hlam, p17751_0]
                · linarith only [h0, h17742, hlam]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                rcases p17740_3 (m.d 0 2) (by simp) with h17790 | h17790
                · rcases p17740_3 (m.d 1 2) (by simp) with h17791 | h17791
                  · linarith only [h0, h17791, hlam]
                  · linarith only [h16969, h17791, hlam]
                · linarith only [h17790, hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                rcases p17740_3 (m.d 0 2) (by simp) with h17795 | h17795
                · rcases p17740_3 (m.d 1 2) (by simp) with h17796 | h17796
                  · linarith only [h0, h17796, hlam]
                  · linarith only [h16970, h17796, hlam]
                · linarith only [h17795, hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                rcases p17740_3 (m.d 0 2) (by simp) with h17800 | h17800
                · rcases p17740_3 (m.d 1 2) (by simp) with h17801 | h17801
                  · linarith only [h0, h17801, hlam]
                  · linarith only [h16971, h17801, hlam]
                · linarith only [h17800, hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h0, hlam, p17740_1]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h17738, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17740_1]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h16978, h17738, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17740_1]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h16978, h16982, h17738, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17740_1]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h4, hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h16969, hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h16978, hlam, p17740_1]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h16980, hlam, p17740_1]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h5, hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h16970, hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h14159, h16970, h2, hc23, hc45, hlam, hphi, ht34, p17740_1]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h16982, hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h6, hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h16971, hlam, p17740_0]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h16971, h17738, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17740_1]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [h16971, h17738, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p17740_1]
              · have p17740_0 := h17740c.1
                have p17740_1 := h17740c.2.1
                have p17740_2 := h17740c.2.2.1
                have p17740_3 := h17740c.2.2.2
                linarith only [hlam, p17740_0]
            · rcases h2bigk with h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c | h17825c
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                rcases p17825_3 (m.d 0 2) (by simp) with h17827 | h17827
                · rcases p17825_3 (m.d 1 2) (by simp) with h17828 | h17828
                  · linarith only [h0, h17828, hlam]
                  · rcases p17825_3 (m.d 2 3) (by simp) with h17830 | h17830
                    · linarith only [h17830, h4, hlam]
                    · rcases p17825_3 (m.d 2 4) (by simp) with h17832 | h17832
                      · linarith only [h17832, h5, hlam]
                      · rcases p17825_3 (m.d 2 5) (by simp) with h17834 | h17834
                        · linarith only [h17834, h6, hlam]
                        · rcases h4bigk with h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c | h17836c
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16984, h7, hc14, hc45, hlam, hphi, p17836_1]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p17836_1]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h7, hlam, p17836_1]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h14159, hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h2, hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16978, h16984, h2, h7, hc23, hc45, hlam, hphi, ht34, p17836_1]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16972, hlam, p17836_1]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16976, hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h5, hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16970, hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16978, hlam, p17836_1]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16982, hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16984, hc04, hc45, hlam, hphi, p17836_1]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16984, hc14, hc45, hlam, hphi, p17836_1]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16978, h16984, hc23, hc45, hlam, hphi, ht34, p17836_1]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h16984, hlam, p17836_0]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            rcases p17836_3 (m.d 0 4) (by simp) with h17857 | h17857
                            · linarith only [h17857, hlam, p17836_0]
                            · rcases p17836_3 (m.d 1 4) (by simp) with h17859 | h17859
                              · linarith only [h16976, h17859, hlam]
                              · rcases p17836_3 (m.d 2 4) (by simp) with h17861 | h17861
                                · linarith only [h16982, h17861, hlam]
                                · rcases p17836_3 (m.d 3 4) (by simp) with h17863 | h17863
                                  · linarith only [h16984, h17863, hlam]
                                  · linarith only [h17863, h7, hlam]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            rcases p17836_3 (m.d 0 4) (by simp) with h17866 | h17866
                            · linarith only [h14159, h17866, hlam]
                            · linarith only [h17866, h2, hlam]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            rcases p17836_3 (m.d 0 4) (by simp) with h17869 | h17869
                            · linarith only [h14159, h17869, hlam]
                            · linarith only [h17869, h5, hlam]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [h1, h16969, h7, hc23, hc45, hlam, hphi, ht34, p17836_1]
                          · have p17836_0 := h17836c.1
                            have p17836_1 := h17836c.2.1
                            have p17836_2 := h17836c.2.2.1
                            have p17836_3 := h17836c.2.2.2
                            linarith only [hlam, p17836_0]
                · linarith only [h0, h17827, hlam]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                rcases p17825_3 (m.d 0 2) (by simp) with h17875 | h17875
                · rcases p17825_3 (m.d 1 2) (by simp) with h17876 | h17876
                  · linarith only [h0, h17876, hlam]
                  · linarith only [h16969, h17876, hlam]
                · linarith only [h17875, hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                rcases p17825_3 (m.d 0 2) (by simp) with h17880 | h17880
                · rcases p17825_3 (m.d 1 2) (by simp) with h17881 | h17881
                  · linarith only [h0, h17881, hlam]
                  · linarith only [h16970, h17881, hlam]
                · linarith only [h17880, hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                rcases p17825_3 (m.d 0 2) (by simp) with h17885 | h17885
                · rcases p17825_3 (m.d 1 2) (by simp) with h17886 | h17886
                  · linarith only [h0, h17886, hlam]
                  · linarith only [h16971, h17886, hlam]
                · linarith only [h17885, hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h0, hlam, p17825_1]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17825_1]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h16978, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17825_1]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h16978, h16982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17825_1]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h4, hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h16969, hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h16978, hlam, p17825_1]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h16980, hlam, p17825_1]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h5, hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h16970, hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h14159, h16970, h2, hc23, hc45, hlam, hphi, ht34, p17825_1]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h16982, hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h6, hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h16971, hlam, p17825_0]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17825_1]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p17727_1, p17825_1]
              · have p17825_0 := h17825c.1
                have p17825_1 := h17825c.2.1
                have p17825_2 := h17825c.2.2.1
                have p17825_3 := h17825c.2.2.2
                linarith only [hlam, p17825_0]
            · rcases h2bigk with h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c | h17910c
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                rcases p17910_3 (m.d 0 2) (by simp) with h17912 | h17912
                · rcases p17910_3 (m.d 1 2) (by simp) with h17913 | h17913
                  · linarith only [h0, h17913, hlam]
                  · rcases p17910_3 (m.d 2 3) (by simp) with h17915 | h17915
                    · linarith only [h17915, h4, hlam]
                    · rcases p17910_3 (m.d 2 4) (by simp) with h17917 | h17917
                      · linarith only [h17917, h5, hlam]
                      · rcases p17910_3 (m.d 2 5) (by simp) with h17919 | h17919
                        · linarith only [h17919, h6, hlam]
                        · rcases h4bigk with h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c | h17921c
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16984, h7, hc14, hc45, hlam, hphi, p17921_1]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p17921_1]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h7, hlam, p17921_1]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h14159, hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h2, hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16978, h16984, h2, h7, hc23, hc45, hlam, hphi, ht34, p17921_1]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16972, hlam, p17921_1]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16976, hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h5, hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16970, hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16978, hlam, p17921_1]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16982, hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16984, hc04, hc45, hlam, hphi, p17921_1]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16970, h16978, h16984, hc23, hc45, hlam, hphi, ht34, p17921_1]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16978, h16984, hc23, hc45, hlam, hphi, ht34, p17921_1]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h16984, hlam, p17921_0]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            rcases p17921_3 (m.d 0 4) (by simp) with h17942 | h17942
                            · linarith only [h17942, hlam, p17921_0]
                            · rcases p17921_3 (m.d 1 4) (by simp) with h17944 | h17944
                              · linarith only [h16976, h17944, hlam]
                              · rcases p17921_3 (m.d 2 4) (by simp) with h17946 | h17946
                                · linarith only [h16982, h17946, hlam]
                                · rcases p17921_3 (m.d 3 4) (by simp) with h17948 | h17948
                                  · linarith only [h16984, h17948, hlam]
                                  · linarith only [h17948, h7, hlam]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            rcases p17921_3 (m.d 0 4) (by simp) with h17951 | h17951
                            · linarith only [h14159, h17951, hlam]
                            · linarith only [h17951, h2, hlam]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            rcases p17921_3 (m.d 0 4) (by simp) with h17954 | h17954
                            · linarith only [h14159, h17954, hlam]
                            · linarith only [h17954, h5, hlam]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [h1, h16969, h7, hc23, hc45, hlam, hphi, ht34, p17921_1]
                          · have p17921_0 := h17921c.1
                            have p17921_1 := h17921c.2.1
                            have p17921_2 := h17921c.2.2.1
                            have p17921_3 := h17921c.2.2.2
                            linarith only [hlam, p17921_0]
                · linarith only [h0, h17912, hlam]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                rcases p17910_3 (m.d 0 2) (by simp) with h17960 | h17960
                · rcases p17910_3 (m.d 1 2) (by simp) with h17961 | h17961
                  · linarith only [h0, h17961, hlam]
                  · linarith only [h16969, h17961, hlam]
                · linarith only [h17960, hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                rcases p17910_3 (m.d 0 2) (by simp) with h17965 | h17965
                · rcases p17910_3 (m.d 1 2) (by simp) with h17966 | h17966
                  · linarith only [h0, h17966, hlam]
                  · linarith only [h16970, h17966, hlam]
                · linarith only [h17965, hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                rcases p17910_3 (m.d 0 2) (by simp) with h17970 | h17970
                · rcases p17910_3 (m.d 1 2) (by simp) with h17971 | h17971
                  · linarith only [h0, h17971, hlam]
                  · linarith only [h16971, h17971, hlam]
                · linarith only [h17970, hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h0, hlam, p17910_1]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17910_1]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h16978, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17910_1]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h16978, h16982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17910_1]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h4, hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h16969, hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h16978, hlam, p17910_1]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h16980, hlam, p17910_1]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h5, hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h16970, hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h14159, h16970, h2, hc23, hc45, hlam, hphi, ht34, p17910_1]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h16982, hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h6, hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h16971, hlam, p17910_0]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17910_1]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p17727_1, p17910_1]
              · have p17910_0 := h17910c.1
                have p17910_1 := h17910c.2.1
                have p17910_2 := h17910c.2.2.1
                have p17910_3 := h17910c.2.2.2
                linarith only [hlam, p17910_0]
            · rcases h2bigk with h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c | h17995c
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                rcases p17995_3 (m.d 0 2) (by simp) with h17997 | h17997
                · rcases p17995_3 (m.d 1 2) (by simp) with h17998 | h17998
                  · linarith only [h0, h17998, hlam]
                  · rcases p17995_3 (m.d 2 3) (by simp) with h18000 | h18000
                    · linarith only [h18000, h4, hlam]
                    · rcases p17995_3 (m.d 2 4) (by simp) with h18002 | h18002
                      · linarith only [h18002, h5, hlam]
                      · rcases p17995_3 (m.d 2 5) (by simp) with h18004 | h18004
                        · linarith only [h18004, h6, hlam]
                        · rcases h4bigk with h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c | h18006c
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16984, h7, hc14, hc45, hlam, hphi, p18006_1]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18006_1]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h7, hlam, p18006_1]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h14159, hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h2, hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16978, h16984, h2, h7, hc23, hc45, hlam, hphi, ht34, p18006_1]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16972, hlam, p18006_1]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16976, hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h5, hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16970, hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16978, hlam, p18006_1]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16982, hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16984, hc04, hc45, hlam, hphi, p18006_1]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16970, h16978, h16984, hc23, hc45, hlam, hphi, ht34, p18006_1]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16978, h16984, hc23, hc45, hlam, hphi, ht34, p18006_1]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h16984, hlam, p18006_0]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            rcases p18006_3 (m.d 0 4) (by simp) with h18027 | h18027
                            · linarith only [h18027, hlam, p18006_0]
                            · rcases p18006_3 (m.d 1 4) (by simp) with h18029 | h18029
                              · linarith only [h16976, h18029, hlam]
                              · rcases p18006_3 (m.d 2 4) (by simp) with h18031 | h18031
                                · linarith only [h16982, h18031, hlam]
                                · rcases p18006_3 (m.d 3 4) (by simp) with h18033 | h18033
                                  · linarith only [h16984, h18033, hlam]
                                  · linarith only [h18033, h7, hlam]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            rcases p18006_3 (m.d 0 4) (by simp) with h18036 | h18036
                            · linarith only [h14159, h18036, hlam]
                            · linarith only [h18036, h2, hlam]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            rcases p18006_3 (m.d 0 4) (by simp) with h18039 | h18039
                            · linarith only [h14159, h18039, hlam]
                            · linarith only [h18039, h5, hlam]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [h1, h16969, h7, hc23, hc45, hlam, hphi, ht34, p18006_1]
                          · have p18006_0 := h18006c.1
                            have p18006_1 := h18006c.2.1
                            have p18006_2 := h18006c.2.2.1
                            have p18006_3 := h18006c.2.2.2
                            linarith only [hlam, p18006_0]
                · linarith only [h0, h17997, hlam]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                rcases p17995_3 (m.d 0 2) (by simp) with h18045 | h18045
                · rcases p17995_3 (m.d 1 2) (by simp) with h18046 | h18046
                  · linarith only [h0, h18046, hlam]
                  · linarith only [h16969, h18046, hlam]
                · linarith only [h18045, hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                rcases p17995_3 (m.d 0 2) (by simp) with h18050 | h18050
                · rcases p17995_3 (m.d 1 2) (by simp) with h18051 | h18051
                  · linarith only [h0, h18051, hlam]
                  · linarith only [h16970, h18051, hlam]
                · linarith only [h18050, hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                rcases p17995_3 (m.d 0 2) (by simp) with h18055 | h18055
                · rcases p17995_3 (m.d 1 2) (by simp) with h18056 | h18056
                  · linarith only [h0, h18056, hlam]
                  · linarith only [h16971, h18056, hlam]
                · linarith only [h18055, hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h0, hlam, p17995_1]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17995_1]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h16978, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17995_1]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h16978, h16982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17995_1]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h4, hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h16969, hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h16978, hlam, p17995_1]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h16980, hlam, p17995_1]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h5, hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h16970, hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h14159, h16970, h2, hc23, hc45, hlam, hphi, ht34, p17995_1]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h16982, hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h6, hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h16971, hlam, p17995_0]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p17995_1]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p17727_1, p17995_1]
              · have p17995_0 := h17995c.1
                have p17995_1 := h17995c.2.1
                have p17995_2 := h17995c.2.2.1
                have p17995_3 := h17995c.2.2.2
                linarith only [hlam, p17995_0]
  · linarith only [h17729, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 0 1) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 0 1) ∧ (m.d 1 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 3) ≤ z)))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  rcases p17727_3 (m.d 0 1) (by simp) with h18081 | h18081
  · rcases p17727_3 (m.d 1 2) (by simp) with h18082 | h18082
    · linarith only [h0, h18082, hlam]
    · linarith only [h16969, h18082, hlam]
  · linarith only [h18081, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 0 1) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 0 1) ∧ (m.d 1 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 4) ≤ z)))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  rcases p17727_3 (m.d 0 1) (by simp) with h18086 | h18086
  · rcases p17727_3 (m.d 1 2) (by simp) with h18087 | h18087
    · linarith only [h0, h18087, hlam]
    · linarith only [h16970, h18087, hlam]
  · linarith only [h18086, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 0 1) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 0 1) ∧ (m.d 1 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 5) ≤ z)))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  rcases p17727_3 (m.d 0 1) (by simp) with h18091 | h18091
  · rcases p17727_3 (m.d 1 2) (by simp) with h18092 | h18092
    · linarith only [h0, h18092, hlam]
    · linarith only [h16971, h18092, hlam]
  · linarith only [h18091, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 2) ∧ (m.d 0 1) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 0 1) ≤ z)))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h0, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 2) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 2) ∧ (m.d 1 2) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 2) ≤ z)))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 2) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 2) ∧ (m.d 1 3) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 3) ≤ z)))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  rcases p17727_3 (m.d 0 1) (by simp) with h18098 | h18098
  · rcases p17727_3 (m.d 1 2) (by simp) with h18099 | h18099
    · rcases p17727_3 (m.d 1 3) (by simp) with h18100 | h18100
      · linarith only [h16969, h18100, hlam]
      · rcases p17727_3 (m.d 1 4) (by simp) with h18102 | h18102
        · linarith only [h16970, h18102, hlam]
        · linarith only [h16972, h18102, hlam]
    · linarith only [h16969, h18099, hlam]
  · linarith only [h1, h18098, hlam]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 2) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 2) ∧ (m.d 1 4) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 4) ≤ z)))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  rcases p17727_3 (m.d 0 1) (by simp) with h18107 | h18107
  · rcases p17727_3 (m.d 1 2) (by simp) with h18108 | h18108
    · rcases p17727_3 (m.d 1 3) (by simp) with h18109 | h18109
      · linarith only [h16969, h18109, hlam]
      · rcases p17727_3 (m.d 1 4) (by simp) with h18111 | h18111
        · linarith only [h16970, h18111, hlam]
        · rcases p17727_3 (m.d 1 5) (by simp) with h18113 | h18113
          · linarith only [h16971, h18113, hlam]
          · linarith only [h16976, h18113, hlam]
    · linarith only [h16970, h18108, hlam]
  · linarith only [h18107, h2, hlam]

end R2N4
