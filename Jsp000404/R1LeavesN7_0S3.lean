import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x0 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x1 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 0 1) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 0 1) ∧ (m.d 1 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 2) ≤ z)))
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
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  rcases p1737_3 (m.d 0 1) (by simp) with h1739 | h1739
  · rcases p1737_3 (m.d 1 2) (by simp) with h1740 | h1740
    · linarith only [h1740, hlam, p1737_0]
    · rcases p1737_3 (m.d 1 3) (by simp) with h1742 | h1742
      · linarith only [h1, h1742, hlam]
      · rcases p1737_3 (m.d 1 4) (by simp) with h1744 | h1744
        · linarith only [h1744, h2, hlam]
        · rcases p1737_3 (m.d 1 5) (by simp) with h1746 | h1746
          · linarith only [h1746, h3, hlam]
          · rcases h1emax with h1748 | h1748 | h1748 | h1748 | h1748
            · linarith only [h1748, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1737_1]
            · rcases h2bigk with h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                rcases p1750_3 (m.d 0 2) (by simp) with h1752 | h1752
                · rcases p1750_3 (m.d 1 2) (by simp) with h1753 | h1753
                  · linarith only [h0, h1753, hlam]
                  · rcases p1750_3 (m.d 2 3) (by simp) with h1755 | h1755
                    · linarith only [h1755, h4, hlam]
                    · rcases p1750_3 (m.d 2 4) (by simp) with h1757 | h1757
                      · linarith only [h1757, h5, hlam]
                      · rcases p1750_3 (m.d 2 5) (by simp) with h1759 | h1759
                        · linarith only [h1759, h6, hlam]
                        · rcases h4bigk with h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            rcases p1761_3 (m.d 0 4) (by simp) with h1763 | h1763
                            · rcases p1761_3 (m.d 1 4) (by simp) with h1764 | h1764
                              · linarith only [h1764, h2, hlam]
                              · rcases p1761_3 (m.d 2 4) (by simp) with h1766 | h1766
                                · linarith only [h1766, h5, hlam]
                                · rcases p1761_3 (m.d 3 4) (by simp) with h1768 | h1768
                                  · linarith only [h1768, h7, hlam]
                                  · linarith only [h13, h1768, hlam]
                            · linarith only [h1763, h2, hlam]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            rcases p1761_3 (m.d 0 4) (by simp) with h1772 | h1772
                            · rcases p1761_3 (m.d 1 4) (by simp) with h1773 | h1773
                              · linarith only [h1773, h2, hlam]
                              · linarith only [h11, h1773, hlam]
                            · linarith only [h1772, h5, hlam]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            rcases p1761_3 (m.d 0 4) (by simp) with h1777 | h1777
                            · rcases p1761_3 (m.d 1 4) (by simp) with h1778 | h1778
                              · linarith only [h1778, h2, hlam]
                              · rcases p1761_3 (m.d 2 4) (by simp) with h1780 | h1780
                                · linarith only [h1780, h5, hlam]
                                · rcases p1761_3 (m.d 3 4) (by simp) with h1782 | h1782
                                  · linarith only [h1782, h7, hlam]
                                  · rcases p1761_3 (m.d 4 5) (by simp) with h1784 | h1784
                                    · linarith only [h1784, h9, hlam]
                                    · linarith only [h1784, h918, hlam]
                            · linarith only [h1777, h7, hlam]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h0, h10, h13, h4, h7, h918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1761_1]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h2, hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h0, h11, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1750_1, p1761_1]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h13, hlam, p1761_1]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h498, hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h5, hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h11, hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h912, hlam, p1761_1]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h916, hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h7, hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h918, hc14, hc45, hlam, hphi, p1761_1]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h0, h4, h7, h9, h918, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1761_1]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h918, hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h9, hlam, p1761_0]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            rcases p1761_3 (m.d 0 4) (by simp) with h1805 | h1805
                            · rcases p1761_3 (m.d 1 4) (by simp) with h1806 | h1806
                              · linarith only [h1806, hlam, p1761_0]
                              · rcases p1761_3 (m.d 2 4) (by simp) with h1808 | h1808
                                · linarith only [h1808, h916, hlam]
                                · rcases p1761_3 (m.d 3 4) (by simp) with h1810 | h1810
                                  · linarith only [h1810, h918, hlam]
                                  · linarith only [h13, h1810, hlam]
                            · linarith only [h1805, h2, hlam]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            rcases p1761_3 (m.d 0 4) (by simp) with h1814 | h1814
                            · rcases p1761_3 (m.d 1 4) (by simp) with h1815 | h1815
                              · linarith only [h1815, h498, hlam]
                              · linarith only [h11, h1815, hlam]
                            · linarith only [h1814, h5, hlam]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [h0, h10, h13, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1761_1]
                          · have p1761_0 := h1761c.1
                            have p1761_1 := h1761c.2.1
                            have p1761_2 := h1761c.2.2.1
                            have p1761_3 := h1761c.2.2.2
                            linarith only [hlam, p1761_0]
                · linarith only [h0, h1752, hlam]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h10, h13, h4, h7, h9, h918, hlam, p1750_2]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                rcases p1750_3 (m.d 0 2) (by simp) with h1823 | h1823
                · rcases p1750_3 (m.d 1 2) (by simp) with h1824 | h1824
                  · linarith only [h0, h1824, hlam]
                  · linarith only [h11, h1824, hlam]
                · linarith only [h1823, hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                rcases p1750_3 (m.d 0 2) (by simp) with h1828 | h1828
                · rcases p1750_3 (m.d 1 2) (by simp) with h1829 | h1829
                  · linarith only [h0, h1829, hlam]
                  · linarith only [h12, h1829, hlam]
                · linarith only [h1828, hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h0, hlam, p1750_1]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h1748, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1750_1]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h1748, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h1748, h916, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h4, hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h10, hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h912, hlam, p1750_1]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h914, hlam, p1750_1]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h5, hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h11, hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h11, h1748, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1750_1]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h916, hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h6, hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h12, hlam, p1750_0]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h12, h1748, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1750_1]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [h12, h1748, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1]
              · have p1750_0 := h1750c.1
                have p1750_1 := h1750c.2.1
                have p1750_2 := h1750c.2.2.1
                have p1750_3 := h1750c.2.2.2
                linarith only [hlam, p1750_0]
            · rcases h2bigk with h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c | h1853c
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                rcases p1853_3 (m.d 0 2) (by simp) with h1855 | h1855
                · rcases p1853_3 (m.d 1 2) (by simp) with h1856 | h1856
                  · linarith only [h0, h1856, hlam]
                  · rcases p1853_3 (m.d 2 3) (by simp) with h1858 | h1858
                    · linarith only [h1858, h4, hlam]
                    · rcases p1853_3 (m.d 2 4) (by simp) with h1860 | h1860
                      · linarith only [h1860, h5, hlam]
                      · rcases p1853_3 (m.d 2 5) (by simp) with h1862 | h1862
                        · linarith only [h1862, h6, hlam]
                        · rcases h4bigk with h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            rcases p1864_3 (m.d 0 4) (by simp) with h1866 | h1866
                            · rcases p1864_3 (m.d 1 4) (by simp) with h1867 | h1867
                              · linarith only [h1867, h2, hlam]
                              · rcases p1864_3 (m.d 2 4) (by simp) with h1869 | h1869
                                · linarith only [h1869, h5, hlam]
                                · rcases p1864_3 (m.d 3 4) (by simp) with h1871 | h1871
                                  · linarith only [h1871, h7, hlam]
                                  · linarith only [h13, h1871, hlam]
                            · linarith only [h1866, h2, hlam]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            rcases p1864_3 (m.d 0 4) (by simp) with h1875 | h1875
                            · rcases p1864_3 (m.d 1 4) (by simp) with h1876 | h1876
                              · linarith only [h1876, h2, hlam]
                              · linarith only [h11, h1876, hlam]
                            · linarith only [h1875, h5, hlam]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            rcases p1864_3 (m.d 0 4) (by simp) with h1880 | h1880
                            · rcases p1864_3 (m.d 1 4) (by simp) with h1881 | h1881
                              · linarith only [h1881, h2, hlam]
                              · rcases p1864_3 (m.d 2 4) (by simp) with h1883 | h1883
                                · linarith only [h1883, h5, hlam]
                                · rcases p1864_3 (m.d 3 4) (by simp) with h1885 | h1885
                                  · linarith only [h1885, h7, hlam]
                                  · rcases p1864_3 (m.d 4 5) (by simp) with h1887 | h1887
                                    · linarith only [h1887, h9, hlam]
                                    · linarith only [h1887, h918, hlam]
                            · linarith only [h1880, h7, hlam]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h10, h13, h7, h918, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h2, hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h11, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p1864_1]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h13, hlam, p1864_1]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h498, hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h5, hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h11, hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h912, hlam, p1864_1]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h916, hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h7, hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h918, hc14, hc45, hlam, hphi, p1864_1]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h0, h4, h7, h9, h918, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1864_1]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h918, hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h9, hlam, p1864_0]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            rcases p1864_3 (m.d 0 4) (by simp) with h1908 | h1908
                            · rcases p1864_3 (m.d 1 4) (by simp) with h1909 | h1909
                              · linarith only [h1909, hlam, p1864_0]
                              · rcases p1864_3 (m.d 2 4) (by simp) with h1911 | h1911
                                · linarith only [h1911, h916, hlam]
                                · rcases p1864_3 (m.d 3 4) (by simp) with h1913 | h1913
                                  · linarith only [h1913, h918, hlam]
                                  · linarith only [h13, h1913, hlam]
                            · linarith only [h1908, h2, hlam]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            rcases p1864_3 (m.d 0 4) (by simp) with h1917 | h1917
                            · rcases p1864_3 (m.d 1 4) (by simp) with h1918 | h1918
                              · linarith only [h1918, h498, hlam]
                              · linarith only [h11, h1918, hlam]
                            · linarith only [h1917, h5, hlam]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [h0, h10, h13, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1]
                          · have p1864_0 := h1864c.1
                            have p1864_1 := h1864c.2.1
                            have p1864_2 := h1864c.2.2.1
                            have p1864_3 := h1864c.2.2.2
                            linarith only [hlam, p1864_0]
                · linarith only [h0, h1855, hlam]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h10, h13, h4, h7, h9, h918, hlam, p1853_2]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                rcases p1853_3 (m.d 0 2) (by simp) with h1926 | h1926
                · rcases p1853_3 (m.d 1 2) (by simp) with h1927 | h1927
                  · linarith only [h0, h1927, hlam]
                  · linarith only [h11, h1927, hlam]
                · linarith only [h1926, hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                rcases p1853_3 (m.d 0 2) (by simp) with h1931 | h1931
                · rcases p1853_3 (m.d 1 2) (by simp) with h1932 | h1932
                  · linarith only [h0, h1932, hlam]
                  · linarith only [h12, h1932, hlam]
                · linarith only [h1931, hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h0, hlam, p1853_1]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p1853_1]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p1853_1]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p1737_1, p1853_1]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h4, hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h10, hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h912, hlam, p1853_1]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h914, hlam, p1853_1]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h5, hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h11, hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p1853_1]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h916, hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h6, hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h12, hlam, p1853_0]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p1853_1]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p1853_1]
              · have p1853_0 := h1853c.1
                have p1853_1 := h1853c.2.1
                have p1853_2 := h1853c.2.2.1
                have p1853_3 := h1853c.2.2.2
                linarith only [hlam, p1853_0]
            · rcases h2bigk with h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                rcases p1956_3 (m.d 0 2) (by simp) with h1958 | h1958
                · rcases p1956_3 (m.d 1 2) (by simp) with h1959 | h1959
                  · linarith only [h0, h1959, hlam]
                  · rcases p1956_3 (m.d 2 3) (by simp) with h1961 | h1961
                    · linarith only [h1961, h4, hlam]
                    · rcases p1956_3 (m.d 2 4) (by simp) with h1963 | h1963
                      · linarith only [h1963, h5, hlam]
                      · rcases p1956_3 (m.d 2 5) (by simp) with h1965 | h1965
                        · linarith only [h1965, h6, hlam]
                        · rcases h4bigk with h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            rcases p1967_3 (m.d 0 4) (by simp) with h1969 | h1969
                            · rcases p1967_3 (m.d 1 4) (by simp) with h1970 | h1970
                              · linarith only [h1970, h2, hlam]
                              · rcases p1967_3 (m.d 2 4) (by simp) with h1972 | h1972
                                · linarith only [h1972, h5, hlam]
                                · rcases p1967_3 (m.d 3 4) (by simp) with h1974 | h1974
                                  · linarith only [h1974, h7, hlam]
                                  · linarith only [h13, h1974, hlam]
                            · linarith only [h1969, h2, hlam]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            rcases p1967_3 (m.d 0 4) (by simp) with h1978 | h1978
                            · rcases p1967_3 (m.d 1 4) (by simp) with h1979 | h1979
                              · linarith only [h1979, h2, hlam]
                              · linarith only [h11, h1979, hlam]
                            · linarith only [h1978, h5, hlam]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            rcases p1967_3 (m.d 0 4) (by simp) with h1983 | h1983
                            · rcases p1967_3 (m.d 1 4) (by simp) with h1984 | h1984
                              · linarith only [h1984, h2, hlam]
                              · rcases p1967_3 (m.d 2 4) (by simp) with h1986 | h1986
                                · linarith only [h1986, h5, hlam]
                                · rcases p1967_3 (m.d 3 4) (by simp) with h1988 | h1988
                                  · linarith only [h1988, h7, hlam]
                                  · rcases p1967_3 (m.d 4 5) (by simp) with h1990 | h1990
                                    · linarith only [h1990, h9, hlam]
                                    · linarith only [h1990, h918, hlam]
                            · linarith only [h1983, h7, hlam]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h10, h13, h7, h918, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1967_1]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h2, hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h0, h11, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1956_1, p1967_1]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h13, hlam, p1967_1]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h498, hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h5, hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h11, hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h912, hlam, p1967_1]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h916, hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h7, hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h918, hc14, hc45, hlam, hphi, p1967_1]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h0, h4, h7, h9, h918, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1967_1]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h918, hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h9, hlam, p1967_0]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            rcases p1967_3 (m.d 0 4) (by simp) with h2011 | h2011
                            · rcases p1967_3 (m.d 1 4) (by simp) with h2012 | h2012
                              · linarith only [h2012, hlam, p1967_0]
                              · rcases p1967_3 (m.d 2 4) (by simp) with h2014 | h2014
                                · linarith only [h2014, h916, hlam]
                                · rcases p1967_3 (m.d 3 4) (by simp) with h2016 | h2016
                                  · linarith only [h2016, h918, hlam]
                                  · linarith only [h13, h2016, hlam]
                            · linarith only [h2, h2011, hlam]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            rcases p1967_3 (m.d 0 4) (by simp) with h2020 | h2020
                            · rcases p1967_3 (m.d 1 4) (by simp) with h2021 | h2021
                              · linarith only [h2021, h498, hlam]
                              · linarith only [h11, h2021, hlam]
                            · linarith only [h2020, h5, hlam]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [h0, h10, h13, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1967_1]
                          · have p1967_0 := h1967c.1
                            have p1967_1 := h1967c.2.1
                            have p1967_2 := h1967c.2.2.1
                            have p1967_3 := h1967c.2.2.2
                            linarith only [hlam, p1967_0]
                · linarith only [h0, h1958, hlam]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h10, h13, h4, h7, h9, h918, hlam, p1956_2]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                rcases p1956_3 (m.d 0 2) (by simp) with h2029 | h2029
                · rcases p1956_3 (m.d 1 2) (by simp) with h2030 | h2030
                  · linarith only [h0, h2030, hlam]
                  · linarith only [h11, h2030, hlam]
                · linarith only [h2029, hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                rcases p1956_3 (m.d 0 2) (by simp) with h2034 | h2034
                · rcases p1956_3 (m.d 1 2) (by simp) with h2035 | h2035
                  · linarith only [h0, h2035, hlam]
                  · linarith only [h12, h2035, hlam]
                · linarith only [h2034, hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h0, hlam, p1956_1]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p1956_1]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p1956_1]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p1737_1, p1956_1]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h4, hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h10, hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h912, hlam, p1956_1]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h914, hlam, p1956_1]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h5, hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h11, hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p1956_1]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h916, hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h6, hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h12, hlam, p1956_0]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p1956_1]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p1956_1]
              · have p1956_0 := h1956c.1
                have p1956_1 := h1956c.2.1
                have p1956_2 := h1956c.2.2.1
                have p1956_3 := h1956c.2.2.2
                linarith only [hlam, p1956_0]
            · rcases h2bigk with h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                rcases p2059_3 (m.d 0 2) (by simp) with h2061 | h2061
                · rcases p2059_3 (m.d 1 2) (by simp) with h2062 | h2062
                  · linarith only [h0, h2062, hlam]
                  · rcases p2059_3 (m.d 2 3) (by simp) with h2064 | h2064
                    · linarith only [h2064, h4, hlam]
                    · rcases p2059_3 (m.d 2 4) (by simp) with h2066 | h2066
                      · linarith only [h2066, h5, hlam]
                      · rcases p2059_3 (m.d 2 5) (by simp) with h2068 | h2068
                        · linarith only [h2068, h6, hlam]
                        · rcases h4bigk with h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            rcases p2070_3 (m.d 0 4) (by simp) with h2072 | h2072
                            · rcases p2070_3 (m.d 1 4) (by simp) with h2073 | h2073
                              · linarith only [h2, h2073, hlam]
                              · rcases p2070_3 (m.d 2 4) (by simp) with h2075 | h2075
                                · linarith only [h2075, h5, hlam]
                                · rcases p2070_3 (m.d 3 4) (by simp) with h2077 | h2077
                                  · linarith only [h2077, h7, hlam]
                                  · linarith only [h13, h2077, hlam]
                            · linarith only [h2, h2072, hlam]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            rcases p2070_3 (m.d 0 4) (by simp) with h2081 | h2081
                            · rcases p2070_3 (m.d 1 4) (by simp) with h2082 | h2082
                              · linarith only [h2, h2082, hlam]
                              · linarith only [h11, h2082, hlam]
                            · linarith only [h2081, h5, hlam]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            rcases p2070_3 (m.d 0 4) (by simp) with h2086 | h2086
                            · rcases p2070_3 (m.d 1 4) (by simp) with h2087 | h2087
                              · linarith only [h2, h2087, hlam]
                              · rcases p2070_3 (m.d 2 4) (by simp) with h2089 | h2089
                                · linarith only [h2089, h5, hlam]
                                · rcases p2070_3 (m.d 3 4) (by simp) with h2091 | h2091
                                  · linarith only [h2091, h7, hlam]
                                  · rcases p2070_3 (m.d 4 5) (by simp) with h2093 | h2093
                                    · linarith only [h2093, h9, hlam]
                                    · linarith only [h2093, h918, hlam]
                            · linarith only [h2086, h7, hlam]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h10, h13, h7, h918, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2070_1]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h2, hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h0, h11, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2059_1, p2070_1]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h13, hlam, p2070_1]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h498, hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h5, hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h11, hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h912, hlam, p2070_1]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h916, hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h7, hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h918, hc14, hc45, hlam, hphi, p2070_1]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h0, h4, h7, h9, h918, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2070_1]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h918, hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h9, hlam, p2070_0]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            rcases p2070_3 (m.d 0 4) (by simp) with h2114 | h2114
                            · rcases p2070_3 (m.d 1 4) (by simp) with h2115 | h2115
                              · linarith only [h2115, hlam, p2070_0]
                              · rcases p2070_3 (m.d 2 4) (by simp) with h2117 | h2117
                                · linarith only [h2117, h916, hlam]
                                · rcases p2070_3 (m.d 3 4) (by simp) with h2119 | h2119
                                  · linarith only [h2119, h918, hlam]
                                  · linarith only [h13, h2119, hlam]
                            · linarith only [h2, h2114, hlam]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            rcases p2070_3 (m.d 0 4) (by simp) with h2123 | h2123
                            · rcases p2070_3 (m.d 1 4) (by simp) with h2124 | h2124
                              · linarith only [h2124, h498, hlam]
                              · linarith only [h11, h2124, hlam]
                            · linarith only [h2123, h5, hlam]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [h0, h10, h13, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2070_1]
                          · have p2070_0 := h2070c.1
                            have p2070_1 := h2070c.2.1
                            have p2070_2 := h2070c.2.2.1
                            have p2070_3 := h2070c.2.2.2
                            linarith only [hlam, p2070_0]
                · linarith only [h0, h2061, hlam]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h10, h13, h4, h7, h9, h918, hlam, p2059_2]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                rcases p2059_3 (m.d 0 2) (by simp) with h2132 | h2132
                · rcases p2059_3 (m.d 1 2) (by simp) with h2133 | h2133
                  · linarith only [h0, h2133, hlam]
                  · linarith only [h11, h2133, hlam]
                · linarith only [h2132, hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                rcases p2059_3 (m.d 0 2) (by simp) with h2137 | h2137
                · rcases p2059_3 (m.d 1 2) (by simp) with h2138 | h2138
                  · linarith only [h0, h2138, hlam]
                  · linarith only [h12, h2138, hlam]
                · linarith only [h2137, hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h0, hlam, p2059_1]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p2059_1]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p2059_1]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p1737_1, p2059_1]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h4, hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h10, hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h912, hlam, p2059_1]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h914, hlam, p2059_1]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h5, hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h11, hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p2059_1]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h916, hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h6, hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h12, hlam, p2059_0]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p2059_1]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p2059_1]
              · have p2059_0 := h2059c.1
                have p2059_1 := h2059c.2.1
                have p2059_2 := h2059c.2.2.1
                have p2059_3 := h2059c.2.2.2
                linarith only [hlam, p2059_0]
  · linarith only [h1739, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x2 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 0 1) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 0 1) ∧ (m.d 1 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 3) ≤ z)))
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
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h0, h13, h4, h7, h9, h918, hlam, p1737_2]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x3 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 0 1) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 0 1) ∧ (m.d 1 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 4) ≤ z)))
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
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  rcases p1737_3 (m.d 0 1) (by simp) with h2164 | h2164
  · rcases p1737_3 (m.d 1 2) (by simp) with h2165 | h2165
    · linarith only [h0, h2165, hlam]
    · linarith only [h11, h2165, hlam]
  · linarith only [h2164, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x4 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 0 1) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 0 1) ∧ (m.d 1 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 5) ≤ z)))
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
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  rcases p1737_3 (m.d 0 1) (by simp) with h2169 | h2169
  · rcases p1737_3 (m.d 1 2) (by simp) with h2170 | h2170
    · linarith only [h0, h2170, hlam]
    · linarith only [h12, h2170, hlam]
  · linarith only [h2169, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x5 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 2) ∧ (m.d 0 1) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 0 1) ≤ z)))
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
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h0, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x6 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 2) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 2) ∧ (m.d 1 2) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 2) ≤ z)))
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
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x7 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 2) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 2) ∧ (m.d 1 3) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 3) ≤ z)))
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
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  rcases p1737_3 (m.d 0 1) (by simp) with h2176 | h2176
  · rcases p1737_3 (m.d 1 2) (by simp) with h2177 | h2177
    · rcases p1737_3 (m.d 1 3) (by simp) with h2178 | h2178
      · linarith only [h10, h2178, hlam]
      · rcases p1737_3 (m.d 1 4) (by simp) with h2180 | h2180
        · linarith only [h11, h2180, hlam]
        · linarith only [h13, h2180, hlam]
    · linarith only [h10, h2177, hlam]
  · linarith only [h1, h2176, hlam]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x8 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 2) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 2) ∧ (m.d 1 4) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 4) ≤ z)))
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
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  rcases p1737_3 (m.d 0 1) (by simp) with h2185 | h2185
  · rcases p1737_3 (m.d 1 2) (by simp) with h2186 | h2186
    · rcases p1737_3 (m.d 1 3) (by simp) with h2187 | h2187
      · linarith only [h10, h2187, hlam]
      · rcases p1737_3 (m.d 1 4) (by simp) with h2189 | h2189
        · linarith only [h11, h2189, hlam]
        · rcases p1737_3 (m.d 1 5) (by simp) with h2191 | h2191
          · linarith only [h12, h2191, hlam]
          · linarith only [h2191, h498, hlam]
    · linarith only [h11, h2186, hlam]
  · linarith only [h2, h2185, hlam]

end R2N4
