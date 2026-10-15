import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h9894 | h9894
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x1 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  linarith only [h0, h9887, h9893, hlam]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h9893 | h9893
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x1 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  linarith only [h0, h9886, h9892, hlam]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h9892 | h9892
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11320 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11321 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11322 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11323 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h11324 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h11325 | h11325
  · rcases m.htr 2 3 5 (by decide) (by decide) with h11326 | h11326
    · rcases m.htr 2 4 5 (by decide) (by decide) with h11327 | h11327
      · linarith only [h11327, h9887, h9891, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h11329 | h11329
        · linarith only [h11325, h11329, h9887, h9891, hlam]
        · rcases h0bigk with h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [hlam, p11331_0]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h0, hlam, p11331_1]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h7600, hlam, p11331_0]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h8836, hlam, p11331_1]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h9666, hlam, p11331_1]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            rcases p11331_3 (m.d 0 1) (by simp) with h11337 | h11337
            · linarith only [h0, h11337, hlam]
            · rcases p11331_3 (m.d 0 2) (by simp) with h11339 | h11339
              · rcases p11331_3 (m.d 0 3) (by simp) with h11340 | h11340
                · linarith only [h11340, h9886, hlam]
                · linarith only [h11340, h7600, hlam]
              · linarith only [h0, h11339, hlam]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [hlam, p11331_0]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h11326, h9886, hc02, hlam, hphi, ht0b, ht5b, p11331_1, u5ehi3]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            rcases p11331_3 (m.d 0 1) (by simp) with h11346 | h11346
            · linarith only [h0, h11346, hlam]
            · rcases p11331_3 (m.d 0 2) (by simp) with h11348 | h11348
              · rcases p11331_3 (m.d 0 3) (by simp) with h11349 | h11349
                · linarith only [h11349, h9886, hlam]
                · linarith only [h11349, h9889, hlam]
              · linarith only [h11348, h9887, hlam]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            rcases p11331_3 (m.d 0 1) (by simp) with h11353 | h11353
            · linarith only [h0, h11353, hlam]
            · rcases p11331_3 (m.d 0 2) (by simp) with h11355 | h11355
              · rcases p11331_3 (m.d 0 3) (by simp) with h11356 | h11356
                · linarith only [h11356, h9886, hlam]
                · linarith only [h11356, h9890, hlam]
              · linarith only [h11355, h9888, hlam]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            rcases p11331_3 (m.d 0 1) (by simp) with h11360 | h11360
            · linarith only [h11360, h7600, hlam]
            · rcases p11331_3 (m.d 0 2) (by simp) with h11362 | h11362
              · rcases p11331_3 (m.d 0 3) (by simp) with h11363 | h11363
                · rcases p11331_3 (m.d 0 4) (by simp) with h11364 | h11364
                  · linarith only [h11364, h9889, hlam]
                  · linarith only [h11364, h8836, hlam]
                · linarith only [h11363, h7600, hlam]
              · linarith only [h0, h11362, hlam]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h9886, hlam, p11331_1]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [hlam, p11331_0]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            rcases p11331_3 (m.d 0 1) (by simp) with h11371 | h11371
            · linarith only [h11371, h7600, hlam]
            · rcases p11331_3 (m.d 0 2) (by simp) with h11373 | h11373
              · rcases p11331_3 (m.d 0 3) (by simp) with h11374 | h11374
                · rcases p11331_3 (m.d 0 4) (by simp) with h11375 | h11375
                  · linarith only [h11375, h9889, hlam]
                  · rcases p11331_3 (m.d 0 5) (by simp) with h11377 | h11377
                    · linarith only [h11377, h9890, hlam]
                    · linarith only [h11377, h9891, hlam]
                · linarith only [h11374, h9889, hlam]
              · linarith only [h11373, h9887, hlam]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            rcases p11331_3 (m.d 0 1) (by simp) with h11382 | h11382
            · linarith only [h11382, h7600, hlam]
            · rcases p11331_3 (m.d 0 2) (by simp) with h11384 | h11384
              · rcases p11331_3 (m.d 0 3) (by simp) with h11385 | h11385
                · rcases p11331_3 (m.d 0 4) (by simp) with h11386 | h11386
                  · linarith only [h11386, h9889, hlam]
                  · rcases p11331_3 (m.d 0 5) (by simp) with h11388 | h11388
                    · linarith only [h11388, h9890, hlam]
                    · rcases h2bigk with h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c | h11390c
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h0, hlam, p11390_1]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h0, h11326, hc12, hlam, hphi, ht01, ht0b, ht5b, p11390_1, u5ehi3]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        rcases p11390_3 (m.d 0 2) (by simp) with h11394 | h11394
                        · rcases p11390_3 (m.d 1 2) (by simp) with h11395 | h11395
                          · rcases p11390_3 (m.d 2 3) (by simp) with h11396 | h11396
                            · linarith only [h11396, h9886, hlam]
                            · linarith only [h11325, h11396, hlam]
                          · linarith only [h11320, h11395, hlam]
                        · linarith only [h11394, hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        rcases p11390_3 (m.d 0 2) (by simp) with h11401 | h11401
                        · rcases p11390_3 (m.d 1 2) (by simp) with h11402 | h11402
                          · rcases p11390_3 (m.d 2 3) (by simp) with h11403 | h11403
                            · linarith only [h11403, h9886, hlam]
                            · linarith only [h11326, h11403, hlam]
                          · linarith only [h11321, h11402, hlam]
                        · linarith only [h11401, hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p11331_1, p11390_1, u5ehi0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h11326, hc12, hlam, hphi, ht01, ht0b, ht5b, p11390_1, u5ehi3]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        rcases p11390_3 (m.d 0 2) (by simp) with h11411 | h11411
                        · linarith only [h0, h11411, hlam]
                        · linarith only [h11411, h9887, hlam]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        rcases p11390_3 (m.d 0 2) (by simp) with h11414 | h11414
                        · linarith only [h0, h11414, hlam]
                        · linarith only [h11414, h9888, hlam]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h9886, hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h11319, hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        rcases p11390_3 (m.d 0 2) (by simp) with h11420 | h11420
                        · rcases p11390_3 (m.d 1 2) (by simp) with h11421 | h11421
                          · rcases p11390_3 (m.d 2 3) (by simp) with h11422 | h11422
                            · rcases p11390_3 (m.d 2 4) (by simp) with h11423 | h11423
                              · linarith only [h11325, h11423, hlam]
                              · rcases p11390_3 (m.d 2 5) (by simp) with h11425 | h11425
                                · linarith only [h11326, h11425, hlam]
                                · linarith only [h11327, h11425, hlam]
                            · linarith only [h11325, h11422, hlam]
                          · linarith only [h11320, h11421, hlam]
                        · linarith only [h11420, h9887, hlam]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h0, h11326, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p11390_1, u5ehi3]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h9887, hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h11320, hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h11325, hlam, p11390_1]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h11327, hlam, p11390_1]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h9888, hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h11321, hlam, p11390_0]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h11326, hlam, p11390_1]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [h9888, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p11331_1, p11390_1]
                      · have p11390_0 := h11390c.1
                        have p11390_1 := h11390c.2.1
                        have p11390_2 := h11390c.2.2.1
                        have p11390_3 := h11390c.2.2.2
                        linarith only [hlam, p11390_0]
                · linarith only [h11385, h9890, hlam]
              · linarith only [h11384, h9888, hlam]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h11324, h9891, hc01, hc14, hlam, hphi, p11331_1]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h9887, hlam, p11331_0]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h9889, hlam, p11331_0]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [hlam, p11331_0]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h9891, hlam, p11331_0]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h11324, h9891, hc01, hc14, hlam, hphi, p11331_1]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h9888, hlam, p11331_1]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h9890, hlam, p11331_0]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [h11324, h8836, h9891, hc01, hc14, hlam, hphi, p11331_1]
          · have p11331_0 := h11331c.1
            have p11331_1 := h11331c.2.1
            have p11331_2 := h11331c.2.2.1
            have p11331_3 := h11331c.2.2.2
            linarith only [hlam, p11331_0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h11454 | h11454
      · linarith only [h11454, h9887, h9891, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h11456 | h11456
        · linarith only [h11325, h11326, h11456, h9890, h9891, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
        · rcases h0bigk with h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c | h11458c
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [hlam, p11458_0]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h0, hlam, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h7600, hlam, p11458_0]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h8836, hlam, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h9666, hlam, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            rcases p11458_3 (m.d 0 1) (by simp) with h11464 | h11464
            · linarith only [h0, h11464, hlam]
            · rcases p11458_3 (m.d 0 2) (by simp) with h11466 | h11466
              · rcases p11458_3 (m.d 0 3) (by simp) with h11467 | h11467
                · linarith only [h11467, h9886, hlam]
                · linarith only [h11467, h7600, hlam]
              · linarith only [h0, h11466, hlam]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [hlam, p11458_0]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h0, h11325, h11326, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            rcases p11458_3 (m.d 0 1) (by simp) with h11473 | h11473
            · linarith only [h0, h11473, hlam]
            · rcases p11458_3 (m.d 0 2) (by simp) with h11475 | h11475
              · rcases p11458_3 (m.d 0 3) (by simp) with h11476 | h11476
                · linarith only [h11476, h9886, hlam]
                · linarith only [h11476, h9889, hlam]
              · linarith only [h11475, h9887, hlam]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h0, h11325, h11326, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            rcases p11458_3 (m.d 0 1) (by simp) with h11481 | h11481
            · linarith only [h11481, h7600, hlam]
            · rcases p11458_3 (m.d 0 2) (by simp) with h11483 | h11483
              · rcases p11458_3 (m.d 0 3) (by simp) with h11484 | h11484
                · rcases p11458_3 (m.d 0 4) (by simp) with h11485 | h11485
                  · linarith only [h11485, h9889, hlam]
                  · linarith only [h11485, h8836, hlam]
                · linarith only [h11484, h7600, hlam]
              · linarith only [h0, h11483, hlam]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h9886, hlam, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [hlam, p11458_0]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            rcases p11458_3 (m.d 0 1) (by simp) with h11492 | h11492
            · linarith only [h11492, h7600, hlam]
            · rcases p11458_3 (m.d 0 2) (by simp) with h11494 | h11494
              · rcases p11458_3 (m.d 0 3) (by simp) with h11495 | h11495
                · rcases p11458_3 (m.d 0 4) (by simp) with h11496 | h11496
                  · linarith only [h11496, h9889, hlam]
                  · rcases p11458_3 (m.d 0 5) (by simp) with h11498 | h11498
                    · linarith only [h11498, h9890, hlam]
                    · linarith only [h11498, h9891, hlam]
                · linarith only [h11495, h9889, hlam]
              · linarith only [h11494, h9887, hlam]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h11325, h11326, h9890, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h9891, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h9887, hlam, p11458_0]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h9889, hlam, p11458_0]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [hlam, p11458_0]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h9891, hlam, p11458_0]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h11319, h11322, h11324, h9891, hc01, hc12, hlam, hphi, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h9888, hlam, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h9890, hlam, p11458_0]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [h11319, h11322, h11324, h8836, h9891, hc01, hc12, hlam, hphi, p11458_1]
          · have p11458_0 := h11458c.1
            have p11458_1 := h11458c.2.1
            have p11458_2 := h11458c.2.2.1
            have p11458_3 := h11458c.2.2.2
            linarith only [hlam, p11458_0]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h11514 | h11514
    · linarith only [h11319, h11325, h11514, h7600, h9889, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h11516 | h11516
      · linarith only [h11325, h11516, h9889, h9891, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h11518 | h11518
        · linarith only [h11518, h9889, h9891, hlam]
        · rcases h0bigk with h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c | h11520c
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [hlam, p11520_0]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h0, hlam, p11520_1]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h7600, hlam, p11520_0]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h8836, hlam, p11520_1]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h9666, hlam, p11520_1]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            rcases p11520_3 (m.d 0 1) (by simp) with h11526 | h11526
            · linarith only [h0, h11526, hlam]
            · rcases p11520_3 (m.d 0 2) (by simp) with h11528 | h11528
              · rcases p11520_3 (m.d 0 3) (by simp) with h11529 | h11529
                · linarith only [h11529, h9886, hlam]
                · linarith only [h11529, h7600, hlam]
              · linarith only [h0, h11528, hlam]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [hlam, p11520_0]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h0, h11325, h9889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11520_1]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            rcases p11520_3 (m.d 0 1) (by simp) with h11535 | h11535
            · linarith only [h0, h11535, hlam]
            · rcases p11520_3 (m.d 0 2) (by simp) with h11537 | h11537
              · rcases p11520_3 (m.d 0 3) (by simp) with h11538 | h11538
                · linarith only [h11538, h9886, hlam]
                · linarith only [h11538, h9889, hlam]
              · linarith only [h11537, h9887, hlam]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            rcases p11520_3 (m.d 0 1) (by simp) with h11542 | h11542
            · linarith only [h0, h11542, hlam]
            · rcases p11520_3 (m.d 0 2) (by simp) with h11544 | h11544
              · rcases p11520_3 (m.d 0 3) (by simp) with h11545 | h11545
                · linarith only [h11545, h9886, hlam]
                · linarith only [h11545, h9890, hlam]
              · linarith only [h11544, h9888, hlam]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            rcases p11520_3 (m.d 0 1) (by simp) with h11549 | h11549
            · linarith only [h11549, h7600, hlam]
            · rcases p11520_3 (m.d 0 2) (by simp) with h11551 | h11551
              · rcases p11520_3 (m.d 0 3) (by simp) with h11552 | h11552
                · rcases p11520_3 (m.d 0 4) (by simp) with h11553 | h11553
                  · linarith only [h11553, h9889, hlam]
                  · linarith only [h11553, h8836, hlam]
                · linarith only [h11552, h7600, hlam]
              · linarith only [h0, h11551, hlam]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h9886, hlam, p11520_1]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [hlam, p11520_0]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            rcases p11520_3 (m.d 0 1) (by simp) with h11560 | h11560
            · linarith only [h11560, h7600, hlam]
            · rcases p11520_3 (m.d 0 2) (by simp) with h11562 | h11562
              · rcases p11520_3 (m.d 0 3) (by simp) with h11563 | h11563
                · rcases p11520_3 (m.d 0 4) (by simp) with h11564 | h11564
                  · linarith only [h11564, h9889, hlam]
                  · rcases p11520_3 (m.d 0 5) (by simp) with h11566 | h11566
                    · linarith only [h11566, h9890, hlam]
                    · linarith only [h11566, h9891, hlam]
                · linarith only [h11563, h9889, hlam]
              · linarith only [h11562, h9887, hlam]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            rcases p11520_3 (m.d 0 1) (by simp) with h11571 | h11571
            · linarith only [h11571, h7600, hlam]
            · rcases p11520_3 (m.d 0 2) (by simp) with h11573 | h11573
              · rcases p11520_3 (m.d 0 3) (by simp) with h11574 | h11574
                · rcases p11520_3 (m.d 0 4) (by simp) with h11575 | h11575
                  · linarith only [h11575, h9889, hlam]
                  · rcases p11520_3 (m.d 0 5) (by simp) with h11577 | h11577
                    · linarith only [h11577, h9890, hlam]
                    · rcases h2bigk with h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c | h11579c
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h0, hlam, p11579_1]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h11325, h9886, h9889, h9891, hlam, p11520_1, p11579_2]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        rcases p11579_3 (m.d 0 2) (by simp) with h11583 | h11583
                        · rcases p11579_3 (m.d 1 2) (by simp) with h11584 | h11584
                          · rcases p11579_3 (m.d 2 3) (by simp) with h11585 | h11585
                            · linarith only [h11585, h9886, hlam]
                            · rcases p11579_3 (m.d 2 4) (by simp) with h11587 | h11587
                              · linarith only [h11587, hlam, p11579_0]
                              · rcases p11579_3 (m.d 2 5) (by simp) with h11589 | h11589
                                · linarith only [h11589, h9888, hlam]
                                · linarith only [h11516, h11589, hlam]
                          · linarith only [h11320, h11584, hlam]
                        · linarith only [h11583, hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        rcases p11579_3 (m.d 0 2) (by simp) with h11594 | h11594
                        · rcases p11579_3 (m.d 1 2) (by simp) with h11595 | h11595
                          · rcases p11579_3 (m.d 2 3) (by simp) with h11596 | h11596
                            · linarith only [h11596, h9886, hlam]
                            · rcases p11579_3 (m.d 2 4) (by simp) with h11598 | h11598
                              · linarith only [h11598, h9887, hlam]
                              · rcases p11579_3 (m.d 2 5) (by simp) with h11600 | h11600
                                · linarith only [h11600, hlam, p11579_0]
                                · rcases h3bigk with h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c | h11602c
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h7600, hlam, p11602_1]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h11325, h9889, h9891, hlam, p11520_1, p11602_2]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    rcases p11602_3 (m.d 0 3) (by simp) with h11606 | h11606
                                    · rcases p11602_3 (m.d 1 3) (by simp) with h11607 | h11607
                                      · rcases p11602_3 (m.d 2 3) (by simp) with h11608 | h11608
                                        · linarith only [h11608, h9886, hlam]
                                        · rcases p11602_3 (m.d 3 4) (by simp) with h11610 | h11610
                                          · linarith only [h11610, hlam, p11602_0]
                                          · rcases p11602_3 (m.d 3 5) (by simp) with h11612 | h11612
                                            · linarith only [h11612, h9890, hlam]
                                            · linarith only [h11518, h11612, hlam]
                                      · linarith only [h11322, h11607, hlam]
                                    · linarith only [h11606, hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    rcases p11602_3 (m.d 0 3) (by simp) with h11617 | h11617
                                    · rcases p11602_3 (m.d 1 3) (by simp) with h11618 | h11618
                                      · rcases p11602_3 (m.d 2 3) (by simp) with h11619 | h11619
                                        · linarith only [h11619, h9886, hlam]
                                        · rcases p11602_3 (m.d 3 4) (by simp) with h11621 | h11621
                                          · linarith only [h11621, h9889, hlam]
                                          · rcases p11602_3 (m.d 3 5) (by simp) with h11623 | h11623
                                            · linarith only [h11623, hlam, p11602_0]
                                            · rcases h5bigk with h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c | h11625c
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [hlam, p11625_0]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h9666, hlam, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h9886, hc02, hlam, hphi, ht0b, ht5b, p11520_1, p11625_1, u5ehi2]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h0, h11325, h11518, h9886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11520_1, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h9891, hlam, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                rcases p11625_3 (m.d 0 5) (by simp) with h11631 | h11631
                                                · linarith only [h11631, h9666, hlam]
                                                · rcases p11625_3 (m.d 1 5) (by simp) with h11633 | h11633
                                                  · rcases p11625_3 (m.d 2 5) (by simp) with h11634 | h11634
                                                    · linarith only [h11321, h11634, hlam]
                                                    · rcases p11625_3 (m.d 3 5) (by simp) with h11636 | h11636
                                                      · linarith only [h11323, h11636, hlam]
                                                      · rcases p11625_3 (m.d 4 5) (by simp) with h11638 | h11638
                                                        · linarith only [h11324, h11638, hlam]
                                                        · linarith only [h11638, h9891, hlam]
                                                  · linarith only [h11633, h9666, hlam]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [hlam, p11625_0]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                rcases p11625_3 (m.d 0 5) (by simp) with h11643 | h11643
                                                · linarith only [h11643, h9666, hlam]
                                                · linarith only [h11643, h9888, hlam]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                rcases p11625_3 (m.d 0 5) (by simp) with h11646 | h11646
                                                · linarith only [h11646, h9666, hlam]
                                                · linarith only [h11646, h9890, hlam]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h11319, h11322, h11324, h11325, h9889, h9891, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h9888, hlam, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h11321, hlam, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [hlam, p11625_0]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h11514, hlam, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h11516, hlam, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h9890, hlam, p11625_0]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h11323, hlam, p11625_0]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h0, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p11602_1, p11625_1, u5ehi2]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [hlam, p11625_0]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h11518, hlam, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h11325, h9889, h9891, hc23, hc45, hlam, hphi, ht34, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h11324, hlam, p11625_0]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h11319, h11322, h11324, hc12, hlam, hphi, ht01, ht0b, ht5b, p11625_1, u5ehi2]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [h11319, h11322, h11324, h11514, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11625_1]
                                              · have p11625_0 := h11625c.1
                                                have p11625_1 := h11625c.2.1
                                                have p11625_2 := h11625c.2.2.1
                                                have p11625_3 := h11625c.2.2.2
                                                linarith only [hlam, p11625_0]
                                      · linarith only [h11323, h11618, hlam]
                                    · linarith only [h11617, hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h11319, h11325, h9889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11602_1]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h11325, h7600, h9889, h9891, hlam, p11520_1, p11602_2]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    rcases p11602_3 (m.d 0 3) (by simp) with h11670 | h11670
                                    · linarith only [h11670, h7600, hlam]
                                    · linarith only [h11670, h9889, hlam]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    rcases p11602_3 (m.d 0 3) (by simp) with h11673 | h11673
                                    · linarith only [h11673, h7600, hlam]
                                    · linarith only [h11673, h9890, hlam]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h9886, hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h11319, hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h11325, hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h11514, hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h9889, hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h11322, hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h9889, h9891, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11520_1, p11602_1]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h11518, hlam, p11602_1]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h9890, hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h11323, hlam, p11602_0]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h0, h9886, h9890, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11520_1, p11602_1]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [h0, h9886, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11520_1, p11602_1]
                                  · have p11602_0 := h11602c.1
                                    have p11602_1 := h11602c.2.1
                                    have p11602_2 := h11602c.2.2.1
                                    have p11602_3 := h11602c.2.2.2
                                    linarith only [hlam, p11602_0]
                          · linarith only [h11321, h11595, hlam]
                        · linarith only [h11594, hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h9886, h9891, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p11520_1, p11579_1]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h11319, h11322, h11324, h11325, h9889, h9891, hlam, p11579_2]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        rcases p11579_3 (m.d 0 2) (by simp) with h11696 | h11696
                        · linarith only [h0, h11696, hlam]
                        · linarith only [h11696, h9887, hlam]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        rcases p11579_3 (m.d 0 2) (by simp) with h11699 | h11699
                        · linarith only [h0, h11699, hlam]
                        · linarith only [h11699, h9888, hlam]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h9886, hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h11319, hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h11325, hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h11514, hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h9887, hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h11320, hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h0, h11325, h9886, h9889, h9891, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11520_1, p11579_1]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h11516, hlam, p11579_1]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h9888, hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h11321, hlam, p11579_0]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h0, h9886, h9888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11520_1, p11579_1]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [h0, h11514, h9886, h9890, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11520_1, p11579_1]
                      · have p11579_0 := h11579c.1
                        have p11579_1 := h11579c.2.1
                        have p11579_2 := h11579c.2.2.1
                        have p11579_3 := h11579c.2.2.2
                        linarith only [hlam, p11579_0]
                · linarith only [h11574, h9890, hlam]
              · linarith only [h11573, h9888, hlam]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h11319, h11322, h11324, h9891, hc01, hc12, hlam, hphi, p11520_1]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h9887, hlam, p11520_0]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h9889, hlam, p11520_0]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [hlam, p11520_0]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h9891, hlam, p11520_0]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h11319, h11322, h11324, h9891, hc01, hc12, hlam, hphi, p11520_1]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h9888, hlam, p11520_1]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h9890, hlam, p11520_0]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [h11319, h11322, h11324, h8836, h9891, hc01, hc12, hlam, hphi, p11520_1]
          · have p11520_0 := h11520c.1
            have p11520_1 := h11520c.2.1
            have p11520_2 := h11520c.2.2.1
            have p11520_3 := h11520c.2.2.2
            linarith only [hlam, p11520_0]

end R2N4
