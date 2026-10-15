import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S15
import Jsp000404.R1LeavesN7_8S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  linarith only [h0, h11319, h9886, hlam]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 1 2 3 (by decide) (by decide) with h11319 | h11319
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 0 4 5 (by decide) (by decide) with h9891 | h9891
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 0 4 5 (by decide) (by decide) with h12390 | h12390
  · linarith only [h12390, h9889, h9890, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12392 | h12392
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12393 | h12393
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12394 | h12394
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12395 | h12395
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12396 | h12396
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12397 | h12397
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12398 | h12398
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12399 | h12399
                  · linarith only [h0, h12399, h7600, h9886, h9890, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12401 | h12401
                    · linarith only [h12390, h12401, h9887, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12403 | h12403
                      · linarith only [h12390, h12396, h12398, h12403, h8836, h9886, h9890, hc01, hc13, hlam, hphi]
                      · rcases h0bigk with h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c | h12405c
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [hlam, p12405_0]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h0, hlam, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h7600, hlam, p12405_0]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h8836, hlam, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h9666, hlam, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          rcases p12405_3 (m.d 0 1) (by simp) with h12411 | h12411
                          · linarith only [h0, h12411, hlam]
                          · rcases p12405_3 (m.d 0 2) (by simp) with h12413 | h12413
                            · rcases p12405_3 (m.d 0 3) (by simp) with h12414 | h12414
                              · linarith only [h12414, h9886, hlam]
                              · linarith only [h12414, h7600, hlam]
                            · linarith only [h0, h12413, hlam]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [hlam, p12405_0]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          rcases p12405_3 (m.d 0 1) (by simp) with h12419 | h12419
                          · linarith only [h0, h12419, hlam]
                          · rcases p12405_3 (m.d 0 2) (by simp) with h12421 | h12421
                            · rcases p12405_3 (m.d 0 3) (by simp) with h12422 | h12422
                              · linarith only [h12422, h9886, hlam]
                              · rcases p12405_3 (m.d 0 4) (by simp) with h12424 | h12424
                                · linarith only [h12424, h9887, hlam]
                                · rcases p12405_3 (m.d 0 5) (by simp) with h12426 | h12426
                                  · linarith only [h12426, h9888, hlam]
                                  · linarith only [h12426, h9890, hlam]
                            · linarith only [h12421, h9886, hlam]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          rcases p12405_3 (m.d 0 1) (by simp) with h12430 | h12430
                          · linarith only [h0, h12430, hlam]
                          · rcases p12405_3 (m.d 0 2) (by simp) with h12432 | h12432
                            · rcases p12405_3 (m.d 0 3) (by simp) with h12433 | h12433
                              · linarith only [h12433, h9886, hlam]
                              · linarith only [h12433, h9889, hlam]
                            · linarith only [h12432, h9887, hlam]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          rcases p12405_3 (m.d 0 1) (by simp) with h12437 | h12437
                          · linarith only [h0, h12437, hlam]
                          · rcases p12405_3 (m.d 0 2) (by simp) with h12439 | h12439
                            · rcases p12405_3 (m.d 0 3) (by simp) with h12440 | h12440
                              · linarith only [h12440, h9886, hlam]
                              · rcases p12405_3 (m.d 0 4) (by simp) with h12442 | h12442
                                · linarith only [h12442, h9887, hlam]
                                · rcases p12405_3 (m.d 0 5) (by simp) with h12444 | h12444
                                  · linarith only [h12444, h9888, hlam]
                                  · rcases h2bigk with h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h0, hlam, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      rcases p12446_3 (m.d 0 2) (by simp) with h12449 | h12449
                                      · rcases p12446_3 (m.d 1 2) (by simp) with h12450 | h12450
                                        · rcases p12446_3 (m.d 2 3) (by simp) with h12451 | h12451
                                          · linarith only [h12451, hlam, p12446_0]
                                          · rcases p12446_3 (m.d 2 4) (by simp) with h12453 | h12453
                                            · linarith only [h12453, h9887, hlam]
                                            · rcases p12446_3 (m.d 2 5) (by simp) with h12455 | h12455
                                              · linarith only [h12455, h9888, hlam]
                                              · linarith only [h12399, h12455, hlam]
                                        · linarith only [h12392, h12450, hlam]
                                      · linarith only [h12449, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      rcases p12446_3 (m.d 0 2) (by simp) with h12460 | h12460
                                      · rcases p12446_3 (m.d 1 2) (by simp) with h12461 | h12461
                                        · rcases p12446_3 (m.d 2 3) (by simp) with h12462 | h12462
                                          · linarith only [h12462, h9886, hlam]
                                          · linarith only [h12398, h12462, hlam]
                                        · linarith only [h12393, h12461, hlam]
                                      · linarith only [h12460, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      rcases p12446_3 (m.d 0 2) (by simp) with h12467 | h12467
                                      · rcases p12446_3 (m.d 1 2) (by simp) with h12468 | h12468
                                        · rcases p12446_3 (m.d 2 3) (by simp) with h12469 | h12469
                                          · linarith only [h12469, h9886, hlam]
                                          · rcases p12446_3 (m.d 2 4) (by simp) with h12471 | h12471
                                            · linarith only [h12471, h9887, hlam]
                                            · rcases p12446_3 (m.d 2 5) (by simp) with h12473 | h12473
                                              · linarith only [h12473, hlam, p12446_0]
                                              · rcases h3bigk with h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c | h12475c
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h7600, hlam, p12475_1]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12392, h12395, h12397, h12398, h12403, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12475_1]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12392, h12395, h12397, h12403, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12475_1]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h9890, hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  rcases p12475_3 (m.d 0 3) (by simp) with h12481 | h12481
                                                  · linarith only [h12481, h7600, hlam]
                                                  · rcases p12475_3 (m.d 1 3) (by simp) with h12483 | h12483
                                                    · rcases p12475_3 (m.d 2 3) (by simp) with h12484 | h12484
                                                      · linarith only [h12392, h12484, hlam]
                                                      · rcases p12475_3 (m.d 3 4) (by simp) with h12486 | h12486
                                                        · linarith only [h12395, h12486, hlam]
                                                        · rcases p12475_3 (m.d 3 5) (by simp) with h12488 | h12488
                                                          · linarith only [h12396, h12488, hlam]
                                                          · linarith only [h12488, h9890, hlam]
                                                    · linarith only [h12483, h7600, hlam]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  rcases p12475_3 (m.d 0 3) (by simp) with h12493 | h12493
                                                  · linarith only [h12493, h7600, hlam]
                                                  · linarith only [h12493, h9886, hlam]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12395, h12397, h12398, h12403, h9886, h9890, hlam, p12475_2]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12392, h12398, h9886, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12475_1]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h9886, hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12392, hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h0, h9886, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12405_1, p12475_1]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12399, hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h9889, hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12395, hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12398, hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12403, hlam, p12475_1]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12392, h12396, h7600, hc01, hc12, hlam, hphi, p12475_1]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12396, hlam, p12475_0]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [h12392, h12396, h12398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12475_1]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  rcases p12475_3 (m.d 0 3) (by simp) with h12511 | h12511
                                                  · linarith only [h12511, h9890, hlam]
                                                  · linarith only [h12511, h9889, hlam]
                                                · have p12475_0 := h12475c.1
                                                  have p12475_1 := h12475c.2.1
                                                  have p12475_2 := h12475c.2.2.1
                                                  have p12475_3 := h12475c.2.2.2
                                                  linarith only [hlam, p12475_0]
                                        · linarith only [h12394, h12468, hlam]
                                      · linarith only [h12467, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p12405_1, p12446_1, u5ehi0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      rcases p12446_3 (m.d 0 2) (by simp) with h12519 | h12519
                                      · linarith only [h0, h12519, hlam]
                                      · linarith only [h12519, h9886, hlam]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      rcases p12446_3 (m.d 0 2) (by simp) with h12522 | h12522
                                      · linarith only [h0, h12522, hlam]
                                      · linarith only [h12522, h9887, hlam]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      rcases p12446_3 (m.d 0 2) (by simp) with h12525 | h12525
                                      · linarith only [h0, h12525, hlam]
                                      · linarith only [h12525, h9888, hlam]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h9886, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12392, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12399, h9888, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p12405_1, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12399, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h9887, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12393, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12398, hlam, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12401, hlam, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h9888, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12394, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h9888, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12405_1, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h0, h12398, h9888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12405_1, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hlam, p12446_0]
                            · linarith only [h12439, h9888, hlam]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h12392, h12395, h12397, h12403, h9890, hc01, hc12, hlam, hphi, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h9886, hlam, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [hlam, p12405_0]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h12392, h12395, h12397, h12403, h8836, h9890, hc01, hc12, hlam, hphi, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h9890, hlam, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h12392, h12395, h12397, h12403, h9889, h9890, hc01, hc12, hlam, hphi, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h9887, hlam, p12405_0]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h9889, hlam, p12405_0]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [hlam, p12405_0]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h12390, hlam, p12405_0]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h12392, h12395, h12397, h12403, h9890, hc01, hc12, hlam, hphi, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h9888, hlam, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h12392, h12395, h12397, h12403, h7600, h9890, hc01, hc12, hlam, hphi, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [h12392, h12395, h12397, h12403, h8836, h9890, hc01, hc12, hlam, hphi, p12405_1]
                        · have p12405_0 := h12405c.1
                          have p12405_1 := h12405c.2.1
                          have p12405_2 := h12405c.2.2.1
                          have p12405_3 := h12405c.2.2.2
                          linarith only [hlam, p12405_0]
                · linarith only [h12398, h9889, h9890, hc23, hc35, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12560 | h12560
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12561 | h12561
                  · linarith only [h0, h12561, h7600, h9886, h9890, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12563 | h12563
                    · linarith only [h12397, h12563, h8836, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12565 | h12565
                      · linarith only [h12396, h12397, h12560, h12565, h9886, h9890, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c | h12567c
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [hlam, p12567_0]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h0, hlam, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h7600, hlam, p12567_0]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h8836, hlam, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h9666, hlam, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          rcases p12567_3 (m.d 0 1) (by simp) with h12573 | h12573
                          · linarith only [h0, h12573, hlam]
                          · rcases p12567_3 (m.d 0 2) (by simp) with h12575 | h12575
                            · rcases p12567_3 (m.d 0 3) (by simp) with h12576 | h12576
                              · linarith only [h12576, h9886, hlam]
                              · linarith only [h12576, h7600, hlam]
                            · linarith only [h0, h12575, hlam]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [hlam, p12567_0]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          rcases p12567_3 (m.d 0 1) (by simp) with h12581 | h12581
                          · linarith only [h0, h12581, hlam]
                          · rcases p12567_3 (m.d 0 2) (by simp) with h12583 | h12583
                            · rcases p12567_3 (m.d 0 3) (by simp) with h12584 | h12584
                              · linarith only [h12584, h9886, hlam]
                              · rcases p12567_3 (m.d 0 4) (by simp) with h12586 | h12586
                                · linarith only [h12586, h9887, hlam]
                                · rcases p12567_3 (m.d 0 5) (by simp) with h12588 | h12588
                                  · linarith only [h12588, h9888, hlam]
                                  · linarith only [h12588, h9890, hlam]
                            · linarith only [h12583, h9886, hlam]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          rcases p12567_3 (m.d 0 1) (by simp) with h12592 | h12592
                          · linarith only [h0, h12592, hlam]
                          · rcases p12567_3 (m.d 0 2) (by simp) with h12594 | h12594
                            · rcases p12567_3 (m.d 0 3) (by simp) with h12595 | h12595
                              · linarith only [h12595, h9886, hlam]
                              · linarith only [h12595, h9889, hlam]
                            · linarith only [h12594, h9887, hlam]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          rcases p12567_3 (m.d 0 1) (by simp) with h12599 | h12599
                          · linarith only [h0, h12599, hlam]
                          · rcases p12567_3 (m.d 0 2) (by simp) with h12601 | h12601
                            · rcases p12567_3 (m.d 0 3) (by simp) with h12602 | h12602
                              · linarith only [h12602, h9886, hlam]
                              · rcases p12567_3 (m.d 0 4) (by simp) with h12604 | h12604
                                · linarith only [h12604, h9887, hlam]
                                · rcases p12567_3 (m.d 0 5) (by simp) with h12606 | h12606
                                  · linarith only [h12606, h9888, hlam]
                                  · rcases h2bigk with h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c | h12608c
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h0, hlam, p12608_1]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      rcases p12608_3 (m.d 0 2) (by simp) with h12611 | h12611
                                      · rcases p12608_3 (m.d 1 2) (by simp) with h12612 | h12612
                                        · rcases p12608_3 (m.d 2 3) (by simp) with h12613 | h12613
                                          · linarith only [h12613, hlam, p12608_0]
                                          · rcases p12608_3 (m.d 2 4) (by simp) with h12615 | h12615
                                            · linarith only [h12615, h9887, hlam]
                                            · rcases p12608_3 (m.d 2 5) (by simp) with h12617 | h12617
                                              · linarith only [h12617, h9888, hlam]
                                              · linarith only [h12561, h12617, hlam]
                                        · linarith only [h12392, h12612, hlam]
                                      · linarith only [h12611, hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      rcases p12608_3 (m.d 0 2) (by simp) with h12622 | h12622
                                      · rcases p12608_3 (m.d 1 2) (by simp) with h12623 | h12623
                                        · rcases p12608_3 (m.d 2 3) (by simp) with h12624 | h12624
                                          · linarith only [h12624, h9886, hlam]
                                          · linarith only [h12560, h12624, hlam]
                                        · linarith only [h12393, h12623, hlam]
                                      · linarith only [h12622, hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      rcases p12608_3 (m.d 0 2) (by simp) with h12629 | h12629
                                      · rcases p12608_3 (m.d 1 2) (by simp) with h12630 | h12630
                                        · rcases p12608_3 (m.d 2 3) (by simp) with h12631 | h12631
                                          · linarith only [h12631, h9886, hlam]
                                          · rcases p12608_3 (m.d 2 4) (by simp) with h12633 | h12633
                                            · linarith only [h12633, h9887, hlam]
                                            · rcases p12608_3 (m.d 2 5) (by simp) with h12635 | h12635
                                              · linarith only [h12635, hlam, p12608_0]
                                              · rcases h3bigk with h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c | h12637c
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h7600, hlam, p12637_1]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h0, h12560, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12567_1, p12637_1]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h0, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12567_1, p12637_1]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h9890, hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  rcases p12637_3 (m.d 0 3) (by simp) with h12643 | h12643
                                                  · linarith only [h12643, h7600, hlam]
                                                  · rcases p12637_3 (m.d 1 3) (by simp) with h12645 | h12645
                                                    · rcases p12637_3 (m.d 2 3) (by simp) with h12646 | h12646
                                                      · linarith only [h12392, h12646, hlam]
                                                      · rcases p12637_3 (m.d 3 4) (by simp) with h12648 | h12648
                                                        · linarith only [h12395, h12648, hlam]
                                                        · rcases p12637_3 (m.d 3 5) (by simp) with h12650 | h12650
                                                          · linarith only [h12396, h12650, hlam]
                                                          · linarith only [h12650, h9890, hlam]
                                                    · linarith only [h12645, h7600, hlam]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  rcases p12637_3 (m.d 0 3) (by simp) with h12655 | h12655
                                                  · linarith only [h12655, h7600, hlam]
                                                  · linarith only [h12655, h9886, hlam]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h12396, h9889, h9890, hlam, p12637_2]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h9889, h9890, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12637_1]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h9886, hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h12392, hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h0, h9886, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12567_1, p12637_1]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h12561, hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h9889, hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h12395, hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h12560, hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h12565, hlam, p12637_1]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h12392, h12396, h7600, hc01, hc12, hlam, hphi, p12637_1]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h12396, hlam, p12637_0]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [h12392, h12396, h12560, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12637_1]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  rcases p12637_3 (m.d 0 3) (by simp) with h12673 | h12673
                                                  · linarith only [h12673, h9890, hlam]
                                                  · linarith only [h12673, h9889, hlam]
                                                · have p12637_0 := h12637c.1
                                                  have p12637_1 := h12637c.2.1
                                                  have p12637_2 := h12637c.2.2.1
                                                  have p12637_3 := h12637c.2.2.2
                                                  linarith only [hlam, p12637_0]
                                        · linarith only [h12394, h12630, hlam]
                                      · linarith only [h12629, hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p12567_1, p12608_1, u5ehi0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      rcases p12608_3 (m.d 0 2) (by simp) with h12681 | h12681
                                      · linarith only [h0, h12681, hlam]
                                      · linarith only [h12681, h9886, hlam]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      rcases p12608_3 (m.d 0 2) (by simp) with h12684 | h12684
                                      · linarith only [h0, h12684, hlam]
                                      · linarith only [h12684, h9887, hlam]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      rcases p12608_3 (m.d 0 2) (by simp) with h12687 | h12687
                                      · linarith only [h0, h12687, hlam]
                                      · linarith only [h12687, h9888, hlam]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h9886, hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h12392, hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h9886, h9890, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p12567_1, p12608_1]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h12561, hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h9887, hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h12393, hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h12560, hlam, p12608_1]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h12563, hlam, p12608_1]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h9888, hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h12394, hlam, p12608_0]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h0, h9888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12567_1, p12608_1]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [h0, h12560, h9888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12567_1, p12608_1]
                                    · have p12608_0 := h12608c.1
                                      have p12608_1 := h12608c.2.1
                                      have p12608_2 := h12608c.2.2.1
                                      have p12608_3 := h12608c.2.2.2
                                      linarith only [hlam, p12608_0]
                            · linarith only [h12601, h9888, hlam]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h12392, h12396, h9890, hc01, hc12, hlam, hphi, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h9886, hlam, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [hlam, p12567_0]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h12392, h12396, h8836, h9890, hc01, hc12, hlam, hphi, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h9890, hlam, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h12397, h8836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h9887, hlam, p12567_0]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h9889, hlam, p12567_0]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [hlam, p12567_0]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h12390, hlam, p12567_0]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h12392, h12396, h9890, hc01, hc12, hlam, hphi, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h9888, hlam, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h12392, h12396, h7600, h9890, hc01, hc12, hlam, hphi, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [h12392, h12396, h8836, h9890, hc01, hc12, hlam, hphi, p12567_1]
                        · have p12567_0 := h12567c.1
                          have p12567_1 := h12567c.2.1
                          have p12567_2 := h12567c.2.2.1
                          have p12567_3 := h12567c.2.2.2
                          linarith only [hlam, p12567_0]
                · linarith only [h12392, h12396, h12560, h9889, h9890, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12722 | h12722
              · linarith only [h12390, h12395, h12396, h12722, h8836, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12724 | h12724
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12725 | h12725
                  · linarith only [h12396, h12725, h7600, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12727 | h12727
                    · linarith only [h0, h12722, h12727, h9666, h9887, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12729 | h12729
                      · linarith only [h12722, h12729, h8836, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h0bigk with h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c | h12731c
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [hlam, p12731_0]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h0, hlam, p12731_1]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h7600, hlam, p12731_0]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h8836, hlam, p12731_1]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h9666, hlam, p12731_1]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          rcases p12731_3 (m.d 0 1) (by simp) with h12737 | h12737
                          · linarith only [h0, h12737, hlam]
                          · rcases p12731_3 (m.d 0 2) (by simp) with h12739 | h12739
                            · rcases p12731_3 (m.d 0 3) (by simp) with h12740 | h12740
                              · linarith only [h12740, h9886, hlam]
                              · linarith only [h12740, h7600, hlam]
                            · linarith only [h0, h12739, hlam]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [hlam, p12731_0]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          rcases p12731_3 (m.d 0 1) (by simp) with h12745 | h12745
                          · linarith only [h0, h12745, hlam]
                          · rcases p12731_3 (m.d 0 2) (by simp) with h12747 | h12747
                            · rcases p12731_3 (m.d 0 3) (by simp) with h12748 | h12748
                              · linarith only [h12748, h9886, hlam]
                              · rcases p12731_3 (m.d 0 4) (by simp) with h12750 | h12750
                                · linarith only [h12750, h9887, hlam]
                                · rcases p12731_3 (m.d 0 5) (by simp) with h12752 | h12752
                                  · linarith only [h12752, h9888, hlam]
                                  · linarith only [h12752, h9890, hlam]
                            · linarith only [h12747, h9886, hlam]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          rcases p12731_3 (m.d 0 1) (by simp) with h12756 | h12756
                          · linarith only [h0, h12756, hlam]
                          · rcases p12731_3 (m.d 0 2) (by simp) with h12758 | h12758
                            · rcases p12731_3 (m.d 0 3) (by simp) with h12759 | h12759
                              · linarith only [h12759, h9886, hlam]
                              · linarith only [h12759, h9889, hlam]
                            · linarith only [h12758, h9887, hlam]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          rcases p12731_3 (m.d 0 1) (by simp) with h12763 | h12763
                          · linarith only [h0, h12763, hlam]
                          · rcases p12731_3 (m.d 0 2) (by simp) with h12765 | h12765
                            · rcases p12731_3 (m.d 0 3) (by simp) with h12766 | h12766
                              · linarith only [h12766, h9886, hlam]
                              · rcases p12731_3 (m.d 0 4) (by simp) with h12768 | h12768
                                · linarith only [h12768, h9887, hlam]
                                · rcases p12731_3 (m.d 0 5) (by simp) with h12770 | h12770
                                  · linarith only [h12770, h9888, hlam]
                                  · rcases h2bigk with h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c | h12772c
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h0, hlam, p12772_1]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      rcases p12772_3 (m.d 0 2) (by simp) with h12775 | h12775
                                      · rcases p12772_3 (m.d 1 2) (by simp) with h12776 | h12776
                                        · rcases p12772_3 (m.d 2 3) (by simp) with h12777 | h12777
                                          · linarith only [h12777, hlam, p12772_0]
                                          · rcases p12772_3 (m.d 2 4) (by simp) with h12779 | h12779
                                            · linarith only [h12779, h9887, hlam]
                                            · rcases p12772_3 (m.d 2 5) (by simp) with h12781 | h12781
                                              · linarith only [h12781, h9888, hlam]
                                              · linarith only [h12725, h12781, hlam]
                                        · linarith only [h12392, h12776, hlam]
                                      · linarith only [h12775, hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      rcases p12772_3 (m.d 0 2) (by simp) with h12786 | h12786
                                      · rcases p12772_3 (m.d 1 2) (by simp) with h12787 | h12787
                                        · rcases p12772_3 (m.d 2 3) (by simp) with h12788 | h12788
                                          · linarith only [h12788, h9886, hlam]
                                          · linarith only [h12724, h12788, hlam]
                                        · linarith only [h12393, h12787, hlam]
                                      · linarith only [h12786, hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      rcases p12772_3 (m.d 0 2) (by simp) with h12793 | h12793
                                      · rcases p12772_3 (m.d 1 2) (by simp) with h12794 | h12794
                                        · rcases p12772_3 (m.d 2 3) (by simp) with h12795 | h12795
                                          · linarith only [h12795, h9886, hlam]
                                          · rcases p12772_3 (m.d 2 4) (by simp) with h12797 | h12797
                                            · linarith only [h12797, h9887, hlam]
                                            · rcases p12772_3 (m.d 2 5) (by simp) with h12799 | h12799
                                              · linarith only [h12799, hlam, p12772_0]
                                              · rcases h3bigk with h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c | h12801c
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h7600, hlam, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h0, h12724, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12731_1, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h0, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12731_1, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h9890, hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12396, hc03, hc35, hlam, hphi, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12396, h12724, h12729, hc34, hc45, hlam, hphi, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12396, h12729, hc34, hc45, hlam, hphi, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12396, hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h9886, hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12392, hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12396, h12729, h7600, h9886, hc34, hc45, hlam, hphi, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12725, hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h9889, hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12395, hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12724, hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [hlam, p12801_0]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12729, hlam, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12729, h9889, hc34, hc45, hlam, hphi, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12729, h7600, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [h12724, h12729, hc34, hc45, hlam, hphi, p12801_1]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  rcases p12801_3 (m.d 0 3) (by simp) with h12825 | h12825
                                                  · linarith only [h12825, h9890, hlam]
                                                  · linarith only [h12825, h9889, hlam]
                                                · have p12801_0 := h12801c.1
                                                  have p12801_1 := h12801c.2.1
                                                  have p12801_2 := h12801c.2.2.1
                                                  have p12801_3 := h12801c.2.2.2
                                                  linarith only [hlam, p12801_0]
                                        · linarith only [h12394, h12794, hlam]
                                      · linarith only [h12793, hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h12724, h9886, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12731_1, p12772_1]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      rcases p12772_3 (m.d 0 2) (by simp) with h12833 | h12833
                                      · linarith only [h0, h12833, hlam]
                                      · linarith only [h12833, h9886, hlam]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      rcases p12772_3 (m.d 0 2) (by simp) with h12836 | h12836
                                      · linarith only [h0, h12836, hlam]
                                      · linarith only [h12836, h9887, hlam]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      rcases p12772_3 (m.d 0 2) (by simp) with h12839 | h12839
                                      · linarith only [h0, h12839, hlam]
                                      · linarith only [h12839, h9888, hlam]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h9886, hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h12392, hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h9886, h9890, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p12731_1, p12772_1]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h12725, hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h9887, hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h12393, hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h12724, hlam, p12772_1]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h12727, hlam, p12772_1]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h9888, hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h12394, hlam, p12772_0]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h0, h9888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12731_1, p12772_1]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [h0, h12724, h9888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12731_1, p12772_1]
                                    · have p12772_0 := h12772c.1
                                      have p12772_1 := h12772c.2.1
                                      have p12772_2 := h12772c.2.2.1
                                      have p12772_3 := h12772c.2.2.2
                                      linarith only [hlam, p12772_0]
                            · linarith only [h12765, h9888, hlam]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h12729, h9890, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12731_1]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h9886, hlam, p12731_1]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [hlam, p12731_0]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h12729, h8836, h9890, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12731_1]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h9890, hlam, p12731_1]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h12729, h9889, h9890, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12731_1]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h9887, hlam, p12731_0]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h9889, hlam, p12731_0]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [hlam, p12731_0]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h12390, hlam, p12731_0]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          rcases p12731_3 (m.d 0 1) (by simp) with h12868 | h12868
                          · linarith only [h12868, h9666, hlam]
                          · rcases p12731_3 (m.d 0 2) (by simp) with h12870 | h12870
                            · rcases p12731_3 (m.d 0 3) (by simp) with h12871 | h12871
                              · linarith only [h12871, h9890, hlam]
                              · linarith only [h12871, h7600, hlam]
                            · linarith only [h0, h12870, hlam]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h9888, hlam, p12731_1]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [h12724, h12729, h9886, h9890, hc34, hc45, hlam, hphi, p12731_1]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          rcases p12731_3 (m.d 0 1) (by simp) with h12877 | h12877
                          · linarith only [h12877, h9666, hlam]
                          · rcases p12731_3 (m.d 0 2) (by simp) with h12879 | h12879
                            · rcases p12731_3 (m.d 0 3) (by simp) with h12880 | h12880
                              · linarith only [h12880, h9890, hlam]
                              · linarith only [h12880, h9889, hlam]
                            · linarith only [h12879, h9887, hlam]
                        · have p12731_0 := h12731c.1
                          have p12731_1 := h12731c.2.1
                          have p12731_2 := h12731c.2.2.1
                          have p12731_3 := h12731c.2.2.2
                          linarith only [hlam, p12731_0]
                · linarith only [h12724, h9889, h9890, hc23, hc35, hlam, hphi]
          · linarith only [h12395, h7600, h9889, hlam]
        · linarith only [h0, h12394, h9888, hlam]
      · linarith only [h0, h12393, h9887, hlam]
    · linarith only [h0, h12392, h9886, hlam]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 0 3 5 (by decide) (by decide) with h9890 | h9890
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890

set_option maxHeartbeats 7972000 in
set_option maxHeartbeats 7972000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17 m hb0 hb2 hb3 hb5 h0 h7600 h8836 h9666 h9886 h9887 h9888 h9889

set_option maxHeartbeats 7972000 in
set_option maxHeartbeats 7972000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  rcases m.htr 0 4 5 (by decide) (by decide) with h12891 | h12891
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12892 | h12892
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12893 | h12893
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12894 | h12894
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12895 | h12895
          · linarith only [h12890, h12895, h9889, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12897 | h12897
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12898 | h12898
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12899 | h12899
                · linarith only [h12895, h12899, h7600, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12901 | h12901
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12902 | h12902
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12903 | h12903
                      · rcases h0bigk with h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c | h12904c
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [hlam, p12904_0]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h0, hlam, p12904_1]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h7600, hlam, p12904_0]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h8836, hlam, p12904_1]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h9666, hlam, p12904_1]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          rcases p12904_3 (m.d 0 1) (by simp) with h12910 | h12910
                          · linarith only [h0, h12910, hlam]
                          · rcases p12904_3 (m.d 0 2) (by simp) with h12912 | h12912
                            · rcases p12904_3 (m.d 0 3) (by simp) with h12913 | h12913
                              · linarith only [h12913, h9886, hlam]
                              · linarith only [h12913, h7600, hlam]
                            · linarith only [h0, h12912, hlam]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [hlam, p12904_0]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h0, h12901, h12903, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p12904_1, u5ehi4]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h0, h12899, h12901, h12903, h9887, hc12, hlam, hphi, ht01, ht0b, ht5b, p12904_1, u5ehi4]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          rcases p12904_3 (m.d 0 1) (by simp) with h12920 | h12920
                          · linarith only [h0, h12920, hlam]
                          · rcases p12904_3 (m.d 0 2) (by simp) with h12922 | h12922
                            · rcases p12904_3 (m.d 0 3) (by simp) with h12923 | h12923
                              · linarith only [h12923, h9886, hlam]
                              · linarith only [h12890, h12923, hlam]
                            · linarith only [h12922, h9888, hlam]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h12895, h7600, hc01, hc34, hlam, hphi, ht12, ht23, p12904_1]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h9886, hlam, p12904_1]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [hlam, p12904_0]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h9889, hlam, p12904_1]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h12895, h7600, h9888, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12904_1, u5ehi2]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          rcases p12904_3 (m.d 0 1) (by simp) with h12932 | h12932
                          · linarith only [h12932, h8836, hlam]
                          · rcases p12904_3 (m.d 0 2) (by simp) with h12934 | h12934
                            · rcases p12904_3 (m.d 0 3) (by simp) with h12935 | h12935
                              · linarith only [h12935, h9889, hlam]
                              · linarith only [h12935, h7600, hlam]
                            · linarith only [h0, h12934, hlam]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h9887, hlam, p12904_0]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h12901, h12903, h9886, hc04, hlam, hphi, ht0b, ht5b, p12904_1, u5ehi4]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [hlam, p12904_0]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          rcases p12904_3 (m.d 0 1) (by simp) with h12942 | h12942
                          · linarith only [h12942, h8836, hlam]
                          · rcases p12904_3 (m.d 0 2) (by simp) with h12944 | h12944
                            · rcases p12904_3 (m.d 0 3) (by simp) with h12945 | h12945
                              · linarith only [h12945, h9889, hlam]
                              · linarith only [h12890, h12945, hlam]
                            · linarith only [h12944, h9888, hlam]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h12895, h12897, h9666, hc01, hc34, hlam, hphi, ht12, ht23, p12904_1]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h9888, hlam, p12904_1]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h12890, hlam, p12904_0]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [h12891, hlam, p12904_1]
                        · have p12904_0 := h12904c.1
                          have p12904_1 := h12904c.2.1
                          have p12904_2 := h12904c.2.2.1
                          have p12904_3 := h12904c.2.2.2
                          linarith only [hlam, p12904_0]
                      · linarith only [h12895, h12903, h7600, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h12890, h12891, h12895, h12899, h12901, h12902, h7600, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · linarith only [h12890, h12895, h12901, h7600, hc23, hc34, hlam, hphi]
              · linarith only [h12890, h12891, h12895, h12898, h7600, h8836, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h12890, h12897, h7600, hlam]
        · linarith only [h0, h12894, h9888, hlam]
      · linarith only [h0, h12893, h9887, hlam]
    · linarith only [h0, h12892, h9886, hlam]
  · linarith only [h12890, h12891, h9889, hlam]

end R2N4
