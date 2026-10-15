import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S1
import Jsp000404.R1LeavesN7_25S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 4 (by decide) (by decide) with h859 | h859
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h859
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h859

set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7

set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h1790 | h1790
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1791 | h1791
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1792 | h1792
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1793 | h1793
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1794 | h1794
          · linarith only [h1794, h6, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1796 | h1796
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1797 | h1797
              · linarith only [h1790, h1797, h5, h6, hc12, hlam, hphi, ht01, u0ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1799 | h1799
                · linarith only [h1796, h1797, h1799, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1801 | h1801
                  · linarith only [h1799, h1801, h5, h6, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases h2bigk with h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h0, h1792, h1796, h1797, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1803_1]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      rcases p1803_3 (m.d 0 2) (by simp) with h1806 | h1806
                      · rcases p1803_3 (m.d 1 2) (by simp) with h1807 | h1807
                        · linarith only [h0, h1807, hlam]
                        · linarith only [h1790, h1807, hlam]
                      · linarith only [h1806, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      rcases p1803_3 (m.d 0 2) (by simp) with h1811 | h1811
                      · rcases p1803_3 (m.d 1 2) (by simp) with h1812 | h1812
                        · linarith only [h0, h1812, hlam]
                        · linarith only [h1791, h1812, hlam]
                      · linarith only [h1811, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      rcases p1803_3 (m.d 0 2) (by simp) with h1816 | h1816
                      · rcases p1803_3 (m.d 1 2) (by simp) with h1817 | h1817
                        · linarith only [h0, h1817, hlam]
                        · linarith only [h1792, h1817, hlam]
                      · linarith only [h1816, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h0, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h0, h1796, h1801, h5, h6, hc01, hc34, hc45, hlam, hphi, p1803_1, u0ehi3]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      rcases p1803_3 (m.d 0 2) (by simp) with h1824 | h1824
                      · rcases p1803_3 (m.d 1 2) (by simp) with h1825 | h1825
                        · rcases p1803_3 (m.d 2 3) (by simp) with h1826 | h1826
                          · linarith only [h1790, h1826, hlam]
                          · linarith only [h1796, h1826, hlam]
                        · linarith only [h1825, hlam, p1803_0]
                      · linarith only [h1824, h3, hlam]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h0, h1796, h1797, h1801, h5, h6, hc01, hc34, hc45, hlam, hphi, p1803_1, u0ehi3]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h2, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h1790, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h1801, h2, h6, hc24, hc45, hlam, hphi, p1803_1]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h1797, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h3, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h1791, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h1796, hlam, p1803_1]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h1799, hlam, p1803_1]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h4, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h1792, hlam, p1803_0]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h0, h1792, h1801, h5, h6, hc01, hc23, hc45, hlam, hphi, ht34, p1803_1, u0ehi3]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [h0, h1792, h1796, h1801, h5, h6, hc01, hc34, hc45, hlam, hphi, p1803_1, u0ehi3]
                    · have p1803_0 := h1803c.1
                      have p1803_1 := h1803c.2.1
                      have p1803_2 := h1803c.2.2.1
                      have p1803_3 := h1803c.2.2.2
                      linarith only [hlam, p1803_0]
            · linarith only [h1796, h5, h6, hc23, hc35, hlam, hphi]
        · linarith only [h1793, h5, h6, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1849 | h1849
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1850 | h1850
          · linarith only [h0, h1790, h1792, h1850, h4, h5, h6, hc01, hlam, hphi, u0ehi3]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1852 | h1852
            · linarith only [h0, h1790, h1792, h1852, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1852, h5, h6, hc23, hc35, hlam, hphi]
        · linarith only [h1849, h5, h6, hc13, hc35, hlam, hphi]
    · linarith only [h1790, h1791, h3, h5, h6, hc23, hc35, hlam, hphi]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1857 | h1857
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1858 | h1858
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1859 | h1859
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1860 | h1860
          · linarith only [h1790, h1857, h1860, h2, h6, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h1790, h1858, h1860, hlam]
        · linarith only [h1790, h1857, h1859, h5, h6, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1864 | h1864
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1865 | h1865
          · linarith only [h1865, h6, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1867 | h1867
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1868 | h1868
              · linarith only [h1868, h2, h6, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1870 | h1870
                · linarith only [h1790, h1857, h1870, h2, h6, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1872 | h1872
                  · linarith only [h1790, h1857, h1858, h1865, h1867, h1870, h1872, h2, h6, hc13, hc35, hlam, hphi]
                  · linarith only [h1790, h1857, h1867, h1872, h2, h6, hc34, hc45, hlam, hphi]
            · linarith only [h1790, h1857, h1867, h5, h6, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · linarith only [h1790, h1857, h1864, h5, h6, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1877 | h1877
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1878 | h1878
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1879 | h1879
          · linarith only [h1879, h6, hc13, hlam, hphi, ht01, u0ehi2]
          · linarith only [h1790, h1877, h1879, hlam]
        · linarith only [h1790, h1877, h1878, h5, h6, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1883 | h1883
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1884 | h1884
          · linarith only [h1884, h6, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1886 | h1886
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1887 | h1887
              · linarith only [h1887, h2, h6, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1889 | h1889
                · linarith only [h1886, h1887, h1889, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1891 | h1891
                  · linarith only [h1889, h1891, h5, h6, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases h2bigk with h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      rcases p1893_3 (m.d 0 2) (by simp) with h1895 | h1895
                      · rcases p1893_3 (m.d 1 2) (by simp) with h1896 | h1896
                        · linarith only [h0, h1896, hlam]
                        · rcases p1893_3 (m.d 2 3) (by simp) with h1898 | h1898
                          · linarith only [h1898, h2, hlam]
                          · linarith only [h1790, h1898, hlam]
                      · linarith only [h0, h1895, hlam]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      rcases p1893_3 (m.d 0 2) (by simp) with h1902 | h1902
                      · rcases p1893_3 (m.d 1 2) (by simp) with h1903 | h1903
                        · linarith only [h0, h1903, hlam]
                        · rcases p1893_3 (m.d 2 3) (by simp) with h1905 | h1905
                          · linarith only [h1905, hlam, p1893_0]
                          · rcases p1893_3 (m.d 2 4) (by simp) with h1907 | h1907
                            · linarith only [h1907, h3, hlam]
                            · rcases p1893_3 (m.d 2 5) (by simp) with h1909 | h1909
                              · linarith only [h1909, h4, hlam]
                              · linarith only [h1887, h1909, hlam]
                      · linarith only [h1902, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      rcases p1893_3 (m.d 0 2) (by simp) with h1913 | h1913
                      · rcases p1893_3 (m.d 1 2) (by simp) with h1914 | h1914
                        · linarith only [h0, h1914, hlam]
                        · rcases p1893_3 (m.d 2 3) (by simp) with h1916 | h1916
                          · linarith only [h1916, h2, hlam]
                          · linarith only [h1886, h1916, hlam]
                      · linarith only [h1913, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      rcases p1893_3 (m.d 0 2) (by simp) with h1920 | h1920
                      · rcases p1893_3 (m.d 1 2) (by simp) with h1921 | h1921
                        · linarith only [h0, h1921, hlam]
                        · rcases p1893_3 (m.d 2 3) (by simp) with h1923 | h1923
                          · linarith only [h1923, h2, hlam]
                          · rcases p1893_3 (m.d 2 4) (by simp) with h1925 | h1925
                            · linarith only [h1925, h3, hlam]
                            · rcases p1893_3 (m.d 2 5) (by simp) with h1927 | h1927
                              · linarith only [h1927, hlam, p1893_0]
                              · rcases h3bigk with h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1883, h1891, h6, hc34, hc45, hlam, hphi, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1857, h1886, h1891, h6, hc12, hc45, hlam, hphi, ht23, ht34, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1891, h6, hc34, hc45, hlam, hphi, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h6, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1790, hlam, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1, h1891, h5, h6, hc01, hc34, hc45, hlam, hphi, p1929_1, u0ehi3]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1884, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h2, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h0, h1891, h2, h5, h6, hc01, hc13, hc45, hlam, hphi, ht34, p1929_1, u0ehi3]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1891, h2, h6, hc34, hc45, hlam, hphi, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1887, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h5, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1883, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1886, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1891, hlam, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1891, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1929_1, u0ehi3]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1883, h1891, hc34, hc45, hlam, hphi, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1891, hc23, hc45, hlam, hphi, ht34, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1891, hc34, hc45, hlam, hphi, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [hlam, p1929_0]
                      · linarith only [h1920, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h0, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h1790, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h1857, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h1877, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h2, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h1891, h2, h6, hc12, hc45, hlam, hphi, ht23, ht34, p1893_1]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h1857, h1891, h2, h6, hc12, hc45, hlam, hphi, ht23, ht34, p1893_1]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h1887, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h3, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h1891, h3, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p1893_1]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h1886, hlam, p1893_1]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h1889, hlam, p1893_1]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h4, hlam, p1893_0]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      rcases p1893_3 (m.d 0 2) (by simp) with h1972 | h1972
                      · rcases p1893_3 (m.d 1 2) (by simp) with h1973 | h1973
                        · linarith only [h1973, hlam, p1893_0]
                        · rcases p1893_3 (m.d 2 3) (by simp) with h1975 | h1975
                          · linarith only [h1887, h1975, hlam]
                          · linarith only [h1790, h1975, hlam]
                      · linarith only [h0, h1972, hlam]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h1790, hc12, hc25, hlam, hphi, p1893_1]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [h0, h1857, h1891, h4, h5, h6, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p1893_1, u0ehi3]
                    · have p1893_0 := h1893c.1
                      have p1893_1 := h1893c.2.1
                      have p1893_2 := h1893c.2.2.1
                      have p1893_3 := h1893c.2.2.2
                      linarith only [hlam, p1893_0]
            · linarith only [h1, h1790, h1883, h1886, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h1883, h5, h6, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6

end R2N4
