import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h790 | h790
  · linarith only [h0, h11, h5, h790, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h792 | h792
    · linarith only [h10, h11, h792, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h794 | h794
      · linarith only [h0, h10, h11, h5, h794, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h796 | h796
        · rcases m.htr 2 3 4 (by decide) (by decide) with h797 | h797
          · linarith only [h0, h10, h11, h5, h792, h797, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h799 | h799
            · linarith only [h0, h10, h11, h4, h7, h794, h797, h799, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h801 | h801
              · rcases m.htr 3 4 5 (by decide) (by decide) with h802 | h802
                · rcases h1bigk with h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    rcases p803_3 (m.d 0 1) (by simp) with h805 | h805
                    · rcases p803_3 (m.d 1 2) (by simp) with h806 | h806
                      · linarith only [h806, hlam, p803_0]
                      · rcases p803_3 (m.d 1 3) (by simp) with h808 | h808
                        · linarith only [h1, h808, hlam]
                        · rcases p803_3 (m.d 1 4) (by simp) with h810 | h810
                          · linarith only [h2, h810, hlam]
                          · linarith only [h11, h810, hlam]
                    · linarith only [h805, hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    rcases p803_3 (m.d 0 1) (by simp) with h814 | h814
                    · rcases p803_3 (m.d 1 2) (by simp) with h815 | h815
                      · linarith only [h0, h815, hlam]
                      · linarith only [h10, h815, hlam]
                    · linarith only [h814, hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h796, hc01, hlam, hphi, ht0b, ht5b, p803_1, u5ehi4]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    rcases p803_3 (m.d 0 1) (by simp) with h820 | h820
                    · rcases p803_3 (m.d 1 2) (by simp) with h821 | h821
                      · linarith only [h0, h821, hlam]
                      · rcases p803_3 (m.d 1 3) (by simp) with h823 | h823
                        · linarith only [h1, h823, hlam]
                        · rcases p803_3 (m.d 1 4) (by simp) with h825 | h825
                          · linarith only [h2, h825, hlam]
                          · linarith only [h796, h825, hlam]
                    · linarith only [h820, hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h0, hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h0, h4, h7, h790, h797, h801, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h11, hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h790, hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h1, hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h10, hlam, p803_1]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h792, hlam, p803_1]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h794, hlam, p803_1]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h2, hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h10, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    rcases p803_3 (m.d 0 1) (by simp) with h841 | h841
                    · rcases p803_3 (m.d 1 2) (by simp) with h842 | h842
                      · linarith only [h11, h842, hlam]
                      · linarith only [h10, h842, hlam]
                    · linarith only [h1, h841, hlam]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h0, h10, h11, h4, h7, h790, h797, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h3, hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    rcases p803_3 (m.d 0 1) (by simp) with h850 | h850
                    · rcases p803_3 (m.d 1 2) (by simp) with h851 | h851
                      · linarith only [h790, h851, hlam]
                      · linarith only [h10, h851, hlam]
                    · linarith only [h1, h850, hlam]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [h796, hlam, p803_0]
                  · have p803_0 := h803c.1
                    have p803_1 := h803c.2.1
                    have p803_2 := h803c.2.2.1
                    have p803_3 := h803c.2.2.2
                    linarith only [hlam, p803_0]
                · linarith only [h0, h10, h11, h4, h7, h797, h802, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h11, h796, h801, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h859 | h859
          · linarith only [h0, h10, h11, h5, h859, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h861 | h861
            · linarith only [h0, h10, h11, h4, h7, h796, h861, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h863 | h863
              · linarith only [h10, h11, h796, h859, h863, hc23, hc34, hlam, hphi]
              · linarith only [h0, h10, h11, h4, h7, h863, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11

set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h866 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h867 | h867
  · linarith only [h0, h10, h4, h867, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h869 | h869
    · rcases m.htr 1 3 5 (by decide) (by decide) with h870 | h870
      · rcases m.htr 1 4 5 (by decide) (by decide) with h871 | h871
        · linarith only [h0, h10, h4, h866, h871, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h873 | h873
          · rcases m.htr 2 3 5 (by decide) (by decide) with h874 | h874
            · rcases m.htr 2 4 5 (by decide) (by decide) with h875 | h875
              · linarith only [h0, h4, h866, h867, h871, h874, h875, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h877 | h877
                · linarith only [h0, h4, h7, h866, h867, h875, h877, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h1bigk with h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    rcases p879_3 (m.d 0 1) (by simp) with h881 | h881
                    · rcases p879_3 (m.d 1 2) (by simp) with h882 | h882
                      · linarith only [h882, hlam, p879_0]
                      · rcases p879_3 (m.d 1 3) (by simp) with h884 | h884
                        · linarith only [h1, h884, hlam]
                        · linarith only [h10, h884, hlam]
                    · linarith only [h881, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h870, hc01, hlam, hphi, ht0b, ht5b, p879_1, u5ehi3]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    rcases p879_3 (m.d 0 1) (by simp) with h889 | h889
                    · rcases p879_3 (m.d 1 2) (by simp) with h890 | h890
                      · linarith only [h0, h890, hlam]
                      · linarith only [h866, h890, hlam]
                    · linarith only [h889, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    rcases p879_3 (m.d 0 1) (by simp) with h894 | h894
                    · rcases p879_3 (m.d 1 2) (by simp) with h895 | h895
                      · linarith only [h0, h895, hlam]
                      · rcases p879_3 (m.d 1 3) (by simp) with h897 | h897
                        · linarith only [h1, h897, hlam]
                        · linarith only [h870, h897, hlam]
                    · linarith only [h894, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h0, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h10, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h867, h875, hc14, hc45, hlam, hphi, p879_1]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h867, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h1, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h0, h10, h4, h866, h873, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p879_1]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    rcases p879_3 (m.d 0 1) (by simp) with h909 | h909
                    · rcases p879_3 (m.d 1 2) (by simp) with h910 | h910
                      · linarith only [h10, h910, hlam]
                      · linarith only [h866, h910, hlam]
                    · linarith only [h2, h909, hlam]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h0, h10, h4, h866, h867, h873, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p879_1]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h2, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h866, hlam, p879_1]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h869, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h871, hlam, p879_1]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h3, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h3, h866, h873, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p879_1]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [h870, hlam, p879_0]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    rcases p879_3 (m.d 0 1) (by simp) with h923 | h923
                    · rcases p879_3 (m.d 1 2) (by simp) with h924 | h924
                      · linarith only [h867, h924, hlam]
                      · linarith only [h866, h924, hlam]
                    · linarith only [h2, h923, hlam]
                  · have p879_0 := h879c.1
                    have p879_1 := h879c.2.1
                    have p879_2 := h879c.2.2.1
                    have p879_3 := h879c.2.2.2
                    linarith only [hlam, p879_0]
            · linarith only [h0, h10, h4, h8, h866, h873, h874, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h4, h7, h866, h873, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h931 | h931
        · linarith only [h0, h10, h4, h866, h931, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h933 | h933
          · rcases m.htr 2 3 5 (by decide) (by decide) with h934 | h934
            · linarith only [h0, h10, h4, h866, h870, h933, h934, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h8, h866, h933, h934, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h4, h7, h866, h933, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h10, h866, h869, hlam]

set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h866 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h939 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  linarith only [h0, h5, h866, h939, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]

set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h866 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h939 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h941 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h942 | h942
  · rcases m.htr 1 4 5 (by decide) (by decide) with h943 | h943
    · rcases m.htr 2 3 4 (by decide) (by decide) with h944 | h944
      · rcases m.htr 2 3 5 (by decide) (by decide) with h945 | h945
        · rcases m.htr 2 4 5 (by decide) (by decide) with h946 | h946
          · rcases m.htr 3 4 5 (by decide) (by decide) with h947 | h947
            · linarith only [h1, h941, h947, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases h1bigk with h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                rcases p949_3 (m.d 0 1) (by simp) with h951 | h951
                · rcases p949_3 (m.d 1 2) (by simp) with h952 | h952
                  · linarith only [h952, hlam, p949_0]
                  · rcases p949_3 (m.d 1 3) (by simp) with h954 | h954
                    · linarith only [h1, h954, hlam]
                    · linarith only [h10, h954, hlam]
                · linarith only [h951, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h941, h943, h947, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h943, h947, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                rcases p949_3 (m.d 0 1) (by simp) with h960 | h960
                · rcases p949_3 (m.d 1 2) (by simp) with h961 | h961
                  · linarith only [h0, h961, hlam]
                  · rcases p949_3 (m.d 1 3) (by simp) with h963 | h963
                    · linarith only [h1, h963, hlam]
                    · linarith only [h942, h963, hlam]
                · linarith only [h960, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h0, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h10, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h866, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h939, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h1, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                rcases p949_3 (m.d 0 1) (by simp) with h973 | h973
                · rcases p949_3 (m.d 1 2) (by simp) with h974 | h974
                  · linarith only [h10, h974, hlam]
                  · rcases p949_3 (m.d 1 3) (by simp) with h976 | h976
                    · rcases p949_3 (m.d 1 4) (by simp) with h977 | h977
                      · linarith only [h941, h977, hlam]
                      · linarith only [h866, h977, hlam]
                    · linarith only [h10, h976, hlam]
                · linarith only [h0, h973, hlam]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h943, h947, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h0, h10, h4, hc01, hlam, hphi, ht0b, ht5b, p949_1, u5ehi1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h2, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                rcases p949_3 (m.d 0 1) (by simp) with h986 | h986
                · rcases p949_3 (m.d 1 2) (by simp) with h987 | h987
                  · linarith only [h866, h987, hlam]
                  · rcases p949_3 (m.d 1 3) (by simp) with h989 | h989
                    · rcases p949_3 (m.d 1 4) (by simp) with h990 | h990
                      · rcases p949_3 (m.d 1 5) (by simp) with h991 | h991
                        · linarith only [h943, h991, hlam]
                        · linarith only [h939, h991, hlam]
                      · linarith only [h866, h990, hlam]
                    · linarith only [h10, h989, hlam]
                · linarith only [h0, h986, hlam]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h941, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h2, h943, h947, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p949_1]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h3, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                rcases p949_3 (m.d 0 1) (by simp) with h1001 | h1001
                · rcases p949_3 (m.d 1 2) (by simp) with h1002 | h1002
                  · linarith only [h1002, h939, hlam]
                  · rcases p949_3 (m.d 1 3) (by simp) with h1004 | h1004
                    · rcases p949_3 (m.d 1 4) (by simp) with h1005 | h1005
                      · rcases p949_3 (m.d 1 5) (by simp) with h1006 | h1006
                        · rcases h1emax with h1007 | h1007 | h1007 | h1007 | h1007
                          · linarith only [h0, h1007, h4, h944, h946, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                          · rcases h3bigk with h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h941, h943, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1009_1, p949_1]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h0, h10, h4, h941, h943, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1009_1, p949_1]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              rcases p1009_3 (m.d 0 3) (by simp) with h1013 | h1013
                              · rcases p1009_3 (m.d 1 3) (by simp) with h1014 | h1014
                                · linarith only [h1, h1014, hlam]
                                · linarith only [h1014, h941, hlam]
                              · linarith only [h1013, hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              rcases p1009_3 (m.d 0 3) (by simp) with h1018 | h1018
                              · rcases p1009_3 (m.d 1 3) (by simp) with h1019 | h1019
                                · linarith only [h1, h1019, hlam]
                                · linarith only [h1019, h942, hlam]
                              · linarith only [h1018, hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h1, hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h10, hlam, p1009_1]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              rcases p1009_3 (m.d 0 3) (by simp) with h1026 | h1026
                              · rcases p1009_3 (m.d 1 3) (by simp) with h1027 | h1027
                                · rcases p1009_3 (m.d 2 3) (by simp) with h1028 | h1028
                                  · rcases p1009_3 (m.d 3 4) (by simp) with h1029 | h1029
                                    · linarith only [h1029, hlam, p1009_0]
                                    · rcases p1009_3 (m.d 3 5) (by simp) with h1031 | h1031
                                      · linarith only [h1031, h942, hlam]
                                      · linarith only [h1031, h947, hlam]
                                  · linarith only [h1028, h944, hlam]
                                · linarith only [h1027, hlam, p1009_0]
                              · linarith only [h1026, h7, hlam]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p1009_1, u5ehi3]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h4, hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h0, h4, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1009_1]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              rcases p1009_3 (m.d 0 3) (by simp) with h1041 | h1041
                              · rcases p1009_3 (m.d 1 3) (by simp) with h1042 | h1042
                                · linarith only [h10, h1042, hlam]
                                · linarith only [h1042, h941, hlam]
                              · linarith only [h1041, h7, hlam]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p1009_1, u5ehi3]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h7, hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h941, hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h944, hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h947, hlam, p1009_1]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h8, hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h942, hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h945, hlam, p1009_0]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [h1, h942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1009_1]
                            · have p1009_0 := h1009c.1
                              have p1009_1 := h1009c.2.1
                              have p1009_2 := h1009c.2.2.1
                              have p1009_3 := h1009c.2.2.2
                              linarith only [hlam, p1009_0]
                          · linarith only [h1007, h941, h943, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p949_1]
                          · linarith only [h1007, h943, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p949_1]
                          · linarith only [h1007, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p949_1]
                        · linarith only [h1006, h939, hlam]
                      · linarith only [h1005, h866, hlam]
                    · linarith only [h10, h1004, hlam]
                · linarith only [h0, h1001, hlam]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h942, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [h943, hlam, p949_0]
              · have p949_0 := h949c.1
                have p949_1 := h949c.2.1
                have p949_2 := h949c.2.2.1
                have p949_3 := h949c.2.2.2
                linarith only [hlam, p949_0]
          · linarith only [h866, h943, h946, hlam]
        · linarith only [h0, h10, h4, h8, h941, h943, h945, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
      · linarith only [h0, h10, h4, h7, h941, h943, h944, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1070 | h1070
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1071 | h1071
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1072 | h1072
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1073 | h1073
            · linarith only [h1073, h941, h943, hlam]
            · rcases h1bigk with h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h0, h1070, h1072, h4, h866, h943, hlam, p1075_2]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h942, hc01, hlam, hphi, ht0b, ht5b, p1075_1, u5ehi3]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h0, h1070, h1072, h4, h943, hlam, p1075_2]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                rcases p1075_3 (m.d 0 1) (by simp) with h1080 | h1080
                · rcases p1075_3 (m.d 1 2) (by simp) with h1081 | h1081
                  · linarith only [h0, h1081, hlam]
                  · rcases p1075_3 (m.d 1 3) (by simp) with h1083 | h1083
                    · linarith only [h1, h1083, hlam]
                    · linarith only [h1083, h942, hlam]
                · linarith only [h1080, hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h0, hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h10, hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h866, hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h939, hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h1, hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                rcases p1075_3 (m.d 0 1) (by simp) with h1093 | h1093
                · rcases p1075_3 (m.d 1 2) (by simp) with h1094 | h1094
                  · linarith only [h10, h1094, hlam]
                  · rcases p1075_3 (m.d 1 3) (by simp) with h1096 | h1096
                    · rcases p1075_3 (m.d 1 4) (by simp) with h1097 | h1097
                      · linarith only [h1097, h941, hlam]
                      · linarith only [h1097, h866, hlam]
                    · linarith only [h10, h1096, hlam]
                · linarith only [h0, h1093, hlam]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                rcases p1075_3 (m.d 0 1) (by simp) with h1103 | h1103
                · rcases p1075_3 (m.d 1 2) (by simp) with h1104 | h1104
                  · linarith only [h10, h1104, hlam]
                  · rcases p1075_3 (m.d 1 3) (by simp) with h1106 | h1106
                    · rcases p1075_3 (m.d 1 4) (by simp) with h1107 | h1107
                      · linarith only [h1107, h941, hlam]
                      · rcases p1075_3 (m.d 1 5) (by simp) with h1109 | h1109
                        · linarith only [h1109, h942, hlam]
                        · linarith only [h1109, h943, hlam]
                    · linarith only [h1106, h941, hlam]
                · linarith only [h1103, h2, hlam]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h1, h942, hc01, hlam, hphi, ht0b, ht5b, p1075_1, u5ehi3]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h2, hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h0, h1070, h1072, h4, h943, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1075_1]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h941, hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h943, hlam, p1075_1]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h3, hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h0, h1070, h1072, h4, h943, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1075_1]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h942, hlam, p1075_0]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [h0, h1070, h1072, h4, h943, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1075_1]
              · have p1075_0 := h1075c.1
                have p1075_1 := h1075c.2.1
                have p1075_2 := h1075c.2.2.1
                have p1075_3 := h1075c.2.2.2
                linarith only [hlam, p1075_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1125 | h1125
            · linarith only [h1072, h1125, h866, hc12, hc34, hlam, hphi, ht23]
            · rcases h1bigk with h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h0, h1072, h4, h7, h866, h9, hlam, p1127_2]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h942, hc01, hlam, hphi, ht0b, ht5b, p1127_1, u5ehi3]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                rcases p1127_3 (m.d 0 1) (by simp) with h1131 | h1131
                · rcases p1127_3 (m.d 1 2) (by simp) with h1132 | h1132
                  · linarith only [h0, h1132, hlam]
                  · rcases p1127_3 (m.d 1 3) (by simp) with h1134 | h1134
                    · linarith only [h1, h1134, hlam]
                    · linarith only [h1134, h941, hlam]
                · linarith only [h1131, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                rcases p1127_3 (m.d 0 1) (by simp) with h1138 | h1138
                · rcases p1127_3 (m.d 1 2) (by simp) with h1139 | h1139
                  · linarith only [h0, h1139, hlam]
                  · rcases p1127_3 (m.d 1 3) (by simp) with h1141 | h1141
                    · linarith only [h1, h1141, hlam]
                    · linarith only [h1141, h942, hlam]
                · linarith only [h1138, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h0, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h10, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h866, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h939, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                rcases p1127_3 (m.d 0 1) (by simp) with h1151 | h1151
                · rcases p1127_3 (m.d 1 2) (by simp) with h1152 | h1152
                  · linarith only [h10, h1152, hlam]
                  · rcases p1127_3 (m.d 1 3) (by simp) with h1154 | h1154
                    · rcases p1127_3 (m.d 1 4) (by simp) with h1155 | h1155
                      · linarith only [h1155, h941, hlam]
                      · linarith only [h1155, h866, hlam]
                    · linarith only [h10, h1154, hlam]
                · linarith only [h0, h1151, hlam]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                rcases p1127_3 (m.d 0 1) (by simp) with h1161 | h1161
                · rcases p1127_3 (m.d 1 2) (by simp) with h1162 | h1162
                  · linarith only [h10, h1162, hlam]
                  · rcases p1127_3 (m.d 1 3) (by simp) with h1164 | h1164
                    · rcases p1127_3 (m.d 1 4) (by simp) with h1165 | h1165
                      · linarith only [h1165, h941, hlam]
                      · rcases p1127_3 (m.d 1 5) (by simp) with h1167 | h1167
                        · linarith only [h1167, h942, hlam]
                        · linarith only [h1167, h943, hlam]
                    · linarith only [h1164, h941, hlam]
                · linarith only [h1161, h2, hlam]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h0, h10, h4, h942, hc01, hlam, hphi, ht0b, ht5b, p1127_1, u5ehi3]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h2, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h0, h1072, h4, h7, h866, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1127_1]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h941, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h943, hlam, p1127_1]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h3, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                rcases p1127_3 (m.d 0 1) (by simp) with h1179 | h1179
                · rcases p1127_3 (m.d 1 2) (by simp) with h1180 | h1180
                  · linarith only [h1180, h939, hlam]
                  · rcases p1127_3 (m.d 1 3) (by simp) with h1182 | h1182
                    · rcases p1127_3 (m.d 1 4) (by simp) with h1183 | h1183
                      · linarith only [h1183, h943, hlam]
                      · linarith only [h1183, h866, hlam]
                    · linarith only [h10, h1182, hlam]
                · linarith only [h0, h1179, hlam]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h942, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                rcases p1127_3 (m.d 0 1) (by simp) with h1189 | h1189
                · rcases p1127_3 (m.d 1 2) (by simp) with h1190 | h1190
                  · linarith only [h1190, h939, hlam]
                  · rcases p1127_3 (m.d 1 3) (by simp) with h1192 | h1192
                    · rcases p1127_3 (m.d 1 4) (by simp) with h1193 | h1193
                      · linarith only [h1193, h943, hlam]
                      · rcases p1127_3 (m.d 1 5) (by simp) with h1195 | h1195
                        · rcases h1emax with h1196 | h1196 | h1196 | h1196 | h1196
                          · linarith only [h0, h1072, h1196, h4, h7, h9, h939, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1127_1]
                          · rcases h3bigk with h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h0, h4, h942, hc01, hlam, hphi, ht0b, ht5b, p1198_1, u5ehi3]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h0, h10, h4, h942, hc01, hlam, hphi, ht0b, ht5b, p1198_1, u5ehi3]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h1072, h7, h9, h939, h941, hlam, p1127_1, p1198_2]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              rcases p1198_3 (m.d 0 3) (by simp) with h1203 | h1203
                              · rcases p1198_3 (m.d 1 3) (by simp) with h1204 | h1204
                                · linarith only [h1, h1204, hlam]
                                · linarith only [h1204, h942, hlam]
                              · linarith only [h1203, hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h1, hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h10, hlam, p1198_1]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              rcases p1198_3 (m.d 0 3) (by simp) with h1211 | h1211
                              · rcases p1198_3 (m.d 1 3) (by simp) with h1212 | h1212
                                · rcases p1198_3 (m.d 2 3) (by simp) with h1213 | h1213
                                  · rcases p1198_3 (m.d 3 4) (by simp) with h1214 | h1214
                                    · linarith only [h1214, hlam, p1198_0]
                                    · rcases p1198_3 (m.d 3 5) (by simp) with h1216 | h1216
                                      · linarith only [h1216, h942, hlam]
                                      · linarith only [h1125, h1216, hlam]
                                  · linarith only [h1070, h1213, hlam]
                                · linarith only [h1212, hlam, p1198_0]
                              · linarith only [h1211, h7, hlam]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p1198_1, u5ehi3]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h4, hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h0, h4, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1198_1]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              rcases p1198_3 (m.d 0 3) (by simp) with h1226 | h1226
                              · rcases p1198_3 (m.d 1 3) (by simp) with h1227 | h1227
                                · linarith only [h10, h1227, hlam]
                                · linarith only [h1227, h941, hlam]
                              · linarith only [h1226, h7, hlam]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p1198_1, u5ehi3]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h7, hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h941, hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h1070, hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h1125, hlam, p1198_1]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h8, hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h942, hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h1071, hlam, p1198_0]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [h1, h942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1198_1]
                            · have p1198_0 := h1198c.1
                              have p1198_1 := h1198c.2.1
                              have p1198_2 := h1198c.2.2.1
                              have p1198_3 := h1198c.2.2.2
                              linarith only [hlam, p1198_0]
                          · linarith only [h1196, h942, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases h3bigk with h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h0, h4, h866, h942, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1127_1, p1243_1]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h0, h10, h4, h866, h942, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1127_1, p1243_1]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h1072, h7, h9, h939, h941, hlam, p1127_1, p1243_2]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              rcases p1243_3 (m.d 0 3) (by simp) with h1248 | h1248
                              · rcases p1243_3 (m.d 1 3) (by simp) with h1249 | h1249
                                · linarith only [h1, h1249, hlam]
                                · linarith only [h1249, h942, hlam]
                              · linarith only [h1248, hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h1, hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h10, hlam, p1243_1]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              rcases p1243_3 (m.d 0 3) (by simp) with h1256 | h1256
                              · rcases p1243_3 (m.d 1 3) (by simp) with h1257 | h1257
                                · rcases p1243_3 (m.d 2 3) (by simp) with h1258 | h1258
                                  · rcases p1243_3 (m.d 3 4) (by simp) with h1259 | h1259
                                    · linarith only [h1259, hlam, p1243_0]
                                    · rcases p1243_3 (m.d 3 5) (by simp) with h1261 | h1261
                                      · linarith only [h1261, h942, hlam]
                                      · linarith only [h1125, h1261, hlam]
                                  · linarith only [h1070, h1258, hlam]
                                · linarith only [h1257, hlam, p1243_0]
                              · linarith only [h1256, h7, hlam]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h0, h10, h4, hc01, hlam, hphi, ht0b, ht5b, p1243_1, u5ehi3]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h4, hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h0, h4, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1243_1]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              rcases p1243_3 (m.d 0 3) (by simp) with h1271 | h1271
                              · rcases p1243_3 (m.d 1 3) (by simp) with h1272 | h1272
                                · linarith only [h10, h1272, hlam]
                                · linarith only [h1272, h941, hlam]
                              · linarith only [h1271, h7, hlam]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p1243_1, u5ehi3]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h7, hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h941, hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h1070, hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h1125, hlam, p1243_1]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h8, hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h942, hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h1071, hlam, p1243_0]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [h1, h942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1243_1]
                            · have p1243_0 := h1243c.1
                              have p1243_1 := h1243c.2.1
                              have p1243_2 := h1243c.2.2.1
                              have p1243_3 := h1243c.2.2.2
                              linarith only [hlam, p1243_0]
                          · linarith only [h1196, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1127_1]
                        · linarith only [h1195, h943, hlam]
                    · linarith only [h1192, h941, hlam]
                · linarith only [h1189, h2, hlam]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [hlam, p1127_0]
        · linarith only [h10, h1071, h942, hlam]
      · linarith only [h0, h10, h1070, h4, h7, h942, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1294 | h1294
    · linarith only [h0, h1294, h4, h8, h941, h942, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1296 | h1296
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1297 | h1297
        · linarith only [h0, h1297, h4, h941, h942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1299 | h1299
          · linarith only [h1294, h1296, h1297, h1299, h8, h866, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1301 | h1301
            · linarith only [h1, h1299, h1301, h941, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h1bigk with h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h0, h1296, h1297, h4, h8, h866, hlam, p1303_2]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                rcases p1303_3 (m.d 0 1) (by simp) with h1306 | h1306
                · rcases p1303_3 (m.d 1 2) (by simp) with h1307 | h1307
                  · linarith only [h0, h1307, hlam]
                  · rcases p1303_3 (m.d 1 3) (by simp) with h1309 | h1309
                    · linarith only [h1309, hlam, p1303_0]
                    · rcases p1303_3 (m.d 1 4) (by simp) with h1311 | h1311
                      · linarith only [h1311, h2, hlam]
                      · rcases p1303_3 (m.d 1 5) (by simp) with h1313 | h1313
                        · linarith only [h1313, h3, hlam]
                        · linarith only [h1313, h942, hlam]
                · linarith only [h1306, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                rcases p1303_3 (m.d 0 1) (by simp) with h1317 | h1317
                · rcases p1303_3 (m.d 1 2) (by simp) with h1318 | h1318
                  · linarith only [h0, h1318, hlam]
                  · rcases p1303_3 (m.d 1 3) (by simp) with h1320 | h1320
                    · linarith only [h1, h1320, hlam]
                    · linarith only [h1320, h941, hlam]
                · linarith only [h1317, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                rcases p1303_3 (m.d 0 1) (by simp) with h1324 | h1324
                · rcases p1303_3 (m.d 1 2) (by simp) with h1325 | h1325
                  · linarith only [h0, h1325, hlam]
                  · rcases p1303_3 (m.d 1 3) (by simp) with h1327 | h1327
                    · linarith only [h1, h1327, hlam]
                    · rcases p1303_3 (m.d 1 4) (by simp) with h1329 | h1329
                      · linarith only [h1329, h2, hlam]
                      · rcases p1303_3 (m.d 1 5) (by simp) with h1331 | h1331
                        · linarith only [h1331, hlam, p1303_0]
                        · rcases h1emax with h1333 | h1333 | h1333 | h1333 | h1333
                          · linarith only [h0, h1296, h1297, h1301, h1333, h4, h7, h866, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases h3bigk with h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              rcases p1335_3 (m.d 0 3) (by simp) with h1337 | h1337
                              · rcases p1335_3 (m.d 1 3) (by simp) with h1338 | h1338
                                · linarith only [h1, h1338, hlam]
                                · rcases p1335_3 (m.d 2 3) (by simp) with h1340 | h1340
                                  · linarith only [h1340, h4, hlam]
                                  · linarith only [h10, h1340, hlam]
                              · linarith only [h1, h1337, hlam]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              rcases p1335_3 (m.d 0 3) (by simp) with h1344 | h1344
                              · rcases p1335_3 (m.d 1 3) (by simp) with h1345 | h1345
                                · linarith only [h1, h1345, hlam]
                                · rcases p1335_3 (m.d 2 3) (by simp) with h1347 | h1347
                                  · linarith only [h1347, h4, hlam]
                                  · rcases p1335_3 (m.d 3 4) (by simp) with h1349 | h1349
                                    · linarith only [h1349, h7, hlam]
                                    · rcases p1335_3 (m.d 3 5) (by simp) with h1351 | h1351
                                      · linarith only [h1351, h8, hlam]
                                      · linarith only [h1297, h1351, hlam]
                              · linarith only [h1344, h4, hlam]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h10, h1297, h1301, h7, h9, h941, hlam, p1335_2]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h0, h1296, h1297, h4, h866, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1335_1]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h1, hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h10, hlam, p1335_1]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h10, h1297, h1301, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1335_1]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h942, hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h4, hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h1297, h1301, h9, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1335_1]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h0, h1297, h1301, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1335_1]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h1297, hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h7, hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h941, hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h1296, hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h1301, hlam, p1335_1]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h8, hlam, p1335_0]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h0, h1301, h4, h7, h9, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1335_1]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [h0, h1296, h1301, h4, h7, h866, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1335_1]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              rcases p1335_3 (m.d 0 3) (by simp) with h1375 | h1375
                              · rcases p1335_3 (m.d 1 3) (by simp) with h1376 | h1376
                                · linarith only [h1376, h942, hlam]
                                · linarith only [h1376, h941, hlam]
                              · linarith only [h1375, h7, hlam]
                            · have p1335_0 := h1335c.1
                              have p1335_1 := h1335c.2.1
                              have p1335_2 := h1335c.2.2.1
                              have p1335_3 := h1335c.2.2.2
                              linarith only [hlam, p1335_0]
                          · rcases h3bigk with h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              rcases p1381_3 (m.d 0 3) (by simp) with h1383 | h1383
                              · rcases p1381_3 (m.d 1 3) (by simp) with h1384 | h1384
                                · linarith only [h1, h1384, hlam]
                                · rcases p1381_3 (m.d 2 3) (by simp) with h1386 | h1386
                                  · linarith only [h1386, h4, hlam]
                                  · linarith only [h10, h1386, hlam]
                              · linarith only [h1, h1383, hlam]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              rcases p1381_3 (m.d 0 3) (by simp) with h1390 | h1390
                              · rcases p1381_3 (m.d 1 3) (by simp) with h1391 | h1391
                                · linarith only [h1, h1391, hlam]
                                · rcases p1381_3 (m.d 2 3) (by simp) with h1393 | h1393
                                  · linarith only [h1393, h4, hlam]
                                  · rcases p1381_3 (m.d 3 4) (by simp) with h1395 | h1395
                                    · linarith only [h1395, h7, hlam]
                                    · rcases p1381_3 (m.d 3 5) (by simp) with h1397 | h1397
                                      · linarith only [h1397, h8, hlam]
                                      · linarith only [h1297, h1397, hlam]
                              · linarith only [h1390, h4, hlam]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h1301, h7, h9, h941, h942, hlam, p1381_2]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h0, h4, h941, h942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1381_1]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h1, hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h10, hlam, p1381_1]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h0, h4, h8, h942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1381_1]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h942, hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h4, hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h0, h4, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1381_1]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h0, h1297, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1381_1]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h1297, hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h7, hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h941, hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h1296, hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h1301, hlam, p1381_1]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h8, hlam, p1381_0]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h0, h4, h8, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1381_1]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [h0, h10, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1381_1]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              rcases p1381_3 (m.d 0 3) (by simp) with h1421 | h1421
                              · rcases p1381_3 (m.d 1 3) (by simp) with h1422 | h1422
                                · linarith only [h1422, h942, hlam]
                                · linarith only [h1422, h941, hlam]
                              · linarith only [h1421, h7, hlam]
                            · have p1381_0 := h1381c.1
                              have p1381_1 := h1381c.2.1
                              have p1381_2 := h1381c.2.2.1
                              have p1381_3 := h1381c.2.2.2
                              linarith only [hlam, p1381_0]
                          · rcases h3bigk with h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              rcases p1427_3 (m.d 0 3) (by simp) with h1429 | h1429
                              · rcases p1427_3 (m.d 1 3) (by simp) with h1430 | h1430
                                · linarith only [h1, h1430, hlam]
                                · rcases p1427_3 (m.d 2 3) (by simp) with h1432 | h1432
                                  · linarith only [h1432, h4, hlam]
                                  · linarith only [h10, h1432, hlam]
                              · linarith only [h1, h1429, hlam]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              rcases p1427_3 (m.d 0 3) (by simp) with h1436 | h1436
                              · rcases p1427_3 (m.d 1 3) (by simp) with h1437 | h1437
                                · linarith only [h1, h1437, hlam]
                                · rcases p1427_3 (m.d 2 3) (by simp) with h1439 | h1439
                                  · linarith only [h1439, h4, hlam]
                                  · rcases p1427_3 (m.d 3 4) (by simp) with h1441 | h1441
                                    · linarith only [h1441, h7, hlam]
                                    · rcases p1427_3 (m.d 3 5) (by simp) with h1443 | h1443
                                      · linarith only [h1443, h8, hlam]
                                      · linarith only [h1297, h1443, hlam]
                              · linarith only [h1436, h4, hlam]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h1301, h7, h9, h941, h942, hlam, p1427_2]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h0, h4, h941, h942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1427_1]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h1, hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h10, hlam, p1427_1]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h0, h4, h8, h942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1427_1]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h942, hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h4, hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h0, h4, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1427_1]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h0, h1297, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1427_1]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h1297, hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h7, hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h941, hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h1296, hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h1301, hlam, p1427_1]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h8, hlam, p1427_0]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h0, h4, h8, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1427_1]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [h0, h10, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1427_1]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              rcases p1427_3 (m.d 0 3) (by simp) with h1467 | h1467
                              · rcases p1427_3 (m.d 1 3) (by simp) with h1468 | h1468
                                · linarith only [h1468, h942, hlam]
                                · linarith only [h1468, h941, hlam]
                              · linarith only [h1467, h7, hlam]
                            · have p1427_0 := h1427c.1
                              have p1427_1 := h1427c.2.1
                              have p1427_2 := h1427c.2.2.1
                              have p1427_3 := h1427c.2.2.2
                              linarith only [hlam, p1427_0]
                          · rcases h3bigk with h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              rcases p1473_3 (m.d 0 3) (by simp) with h1475 | h1475
                              · rcases p1473_3 (m.d 1 3) (by simp) with h1476 | h1476
                                · linarith only [h1, h1476, hlam]
                                · rcases p1473_3 (m.d 2 3) (by simp) with h1478 | h1478
                                  · linarith only [h1478, h4, hlam]
                                  · linarith only [h10, h1478, hlam]
                              · linarith only [h1, h1475, hlam]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              rcases p1473_3 (m.d 0 3) (by simp) with h1482 | h1482
                              · rcases p1473_3 (m.d 1 3) (by simp) with h1483 | h1483
                                · linarith only [h1, h1483, hlam]
                                · rcases p1473_3 (m.d 2 3) (by simp) with h1485 | h1485
                                  · linarith only [h1485, h4, hlam]
                                  · rcases p1473_3 (m.d 3 4) (by simp) with h1487 | h1487
                                    · linarith only [h1487, h7, hlam]
                                    · rcases p1473_3 (m.d 3 5) (by simp) with h1489 | h1489
                                      · linarith only [h1489, h8, hlam]
                                      · linarith only [h1297, h1489, hlam]
                              · linarith only [h1482, h4, hlam]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h1301, h7, h9, h941, h942, hlam, p1473_2]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h0, h4, h941, h942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1473_1]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h1, hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h10, hlam, p1473_1]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h0, h4, h8, h942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1473_1]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h942, hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h4, hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h0, h4, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1473_1]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h0, h1297, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1473_1]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h1297, hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h7, hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h941, hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h1296, hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h1301, hlam, p1473_1]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h8, hlam, p1473_0]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h0, h4, h8, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1473_1]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [h0, h10, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1473_1]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              rcases p1473_3 (m.d 0 3) (by simp) with h1513 | h1513
                              · rcases p1473_3 (m.d 1 3) (by simp) with h1514 | h1514
                                · linarith only [h1514, h942, hlam]
                                · linarith only [h1514, h941, hlam]
                              · linarith only [h1513, h7, hlam]
                            · have p1473_0 := h1473c.1
                              have p1473_1 := h1473c.2.1
                              have p1473_2 := h1473c.2.2.1
                              have p1473_3 := h1473c.2.2.2
                              linarith only [hlam, p1473_0]
                · linarith only [h1324, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h0, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h10, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h866, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h939, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h1, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h0, h1301, h4, h7, h9, h942, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1303_1]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h0, h1301, h4, h7, h866, h9, h942, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1303_1]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h942, hlam, p1303_1]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h2, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h0, h1301, h4, h7, h9, h941, h942, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1303_1]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h941, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h1294, hlam, p1303_1]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h3, hlam, p1303_0]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                rcases p1303_3 (m.d 0 1) (by simp) with h1536 | h1536
                · rcases p1303_3 (m.d 1 2) (by simp) with h1537 | h1537
                  · linarith only [h1537, h939, hlam]
                  · rcases p1303_3 (m.d 1 3) (by simp) with h1539 | h1539
                    · linarith only [h1539, h942, hlam]
                    · linarith only [h10, h1539, hlam]
                · linarith only [h0, h1536, hlam]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [h0, h1297, h1301, h4, h7, h9, h939, h941, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1303_1]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                rcases p1303_3 (m.d 0 1) (by simp) with h1544 | h1544
                · rcases p1303_3 (m.d 1 2) (by simp) with h1545 | h1545
                  · linarith only [h1545, h939, hlam]
                  · rcases p1303_3 (m.d 1 3) (by simp) with h1547 | h1547
                    · linarith only [h1547, h942, hlam]
                    · linarith only [h1547, h941, hlam]
                · linarith only [h1544, h2, hlam]
              · have p1303_0 := h1303c.1
                have p1303_1 := h1303c.2.1
                have p1303_2 := h1303c.2.2.1
                have p1303_3 := h1303c.2.2.2
                linarith only [hlam, p1303_0]
      · linarith only [h1, h10, h1296, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

end R2N4
