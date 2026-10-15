import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S4
import Jsp000404.R1LeavesN7_27S6
import Jsp000404.R1LeavesN7_27S7
import Jsp000404.R1LeavesN7_27S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4439 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h4562 | h4562
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h4439 h4562
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h4439 h4562

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4439 | h4439
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h4439
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h4439

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3333 | h3333
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h3265 | h3265
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h3104 | h3104
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h2914 h3104
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h2914 h3104

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h2914 | h2914
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x0 m hb0 hb2 hb3 hb5 hg0 h2914
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1 m hb0 hb2 hb3 hb5 hg0 h2914

set_option maxHeartbeats 10930000 in
set_option maxHeartbeats 10930000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1 m hb0 hb2 hb3 hb5 h0

set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h5 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h6 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
  · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
    · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
      · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
        · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
          · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
            · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                · rcases h5bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h0, h12, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h0, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h1, hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h12, hc35, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo4]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h0, h10, hc45, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h3, hlam, p15_1]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h7, hlam, p15_1]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h3, hc02, hc35, hlam, hphi, ht0b, ht5b, p15_1]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h0, h10, h7, hc45, hlam, hphi, ht01, ht0b, ht5b, p15_1, u1elo0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h4, hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h9, hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h12, hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h4, hc03, hc45, hlam, hphi, ht0b, ht5b, p15_1]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h5, hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h10, hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h13, hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [h14, hlam, p15_0]
                  · have p15_0 := h15c.1
                    have p15_1 := h15c.2.1
                    have p15_2 := h15c.2.2.1
                    have p15_3 := h15c.2.2.2
                    linarith only [hlam, p15_0]
                · linarith only [h0, h10, h14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h0, h10, h13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h11, h12, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
            · linarith only [h11, h44, h8, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
              · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                · rcases h5bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p48_1, u1elo0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h0, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p48_1, u1elo0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h0, h44, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p48_1, u1elo0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p48_1, u1elo0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h1, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p48_1, u1elo4]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h1, h44, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p48_1, u1elo0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h0, h10, hc45, hlam, hphi, ht01, ht0b, ht5b, p48_1, u1elo0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h3, hlam, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h7, hlam, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h44, hlam, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h3, hc02, hc45, hlam, hphi, ht0b, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h4, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h9, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h4, hc03, hc25, hlam, hphi, ht0b, ht5b, p48_1]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h0, h10, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, p48_1, u1elo0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h5, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h10, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h46, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [h47, hlam, p48_0]
                  · have p48_0 := h48c.1
                    have p48_1 := h48c.2.1
                    have p48_2 := h48c.2.2.1
                    have p48_3 := h48c.2.2.2
                    linarith only [hlam, p48_0]
                · linarith only [h46, h47, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · linarith only [h0, h10, h46, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
          · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
            · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
              · linarith only [h10, h6, h78, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                · linarith only [h10, h6, h76, h80, hlam]
                · rcases h5bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [hlam, p82_0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p82_1, u1elo0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h0, h5, h77, hc35, hlam, hphi, ht01, ht0b, ht5b, p82_1, u1elo0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h0, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p82_1, u1elo0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h0, h10, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p82_1, u1elo0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h1, hlam, p82_0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [hlam, p82_0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h77, hc35, hlam, hphi, ht01, ht0b, ht5b, p82_1, u1elo4]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p82_1, u1elo0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h10, hlam, p82_1]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h3, hlam, p82_1]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h7, hlam, p82_1]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [hlam, p82_0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h3, hc02, hc35, hlam, hphi, ht0b, ht5b, p82_1]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h78, hlam, p82_1]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h4, hlam, p82_0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h9, hlam, p82_0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h77, hlam, p82_0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [hlam, p82_0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h80, hlam, p82_1]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h5, hlam, p82_0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p82_1, u1elo0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h0, h5, h77, hc35, hlam, hphi, ht01, ht0b, ht5b, p82_1, u1elo0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [h0, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, p82_1, u1elo0]
                  · have p82_0 := h82c.1
                    have p82_1 := h82c.2.1
                    have p82_2 := h82c.2.2.1
                    have p82_3 := h82c.2.2.2
                    linarith only [hlam, p82_0]
            · linarith only [h76, h77, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · linarith only [h0, h10, h5, h76, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
        · linarith only [h110, h8, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
          · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
            · linarith only [h113, h7, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h115 | h115
              · linarith only [h110, h115, h6, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h117 | h117
                · linarith only [h110, h117, h8, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · linarith only [h0, h117, h5, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · linarith only [h112, h8, h9, hc23, hc35, hlam, hphi]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
      · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
        · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
          · linarith only [h123, h6, h8, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
            · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
              · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                · rcases h5bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h0, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h0, h127, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h1, hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo4]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h121, h127, hc45, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo2]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h0, h121, h8, hc45, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h3, hlam, p128_1]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h7, hlam, p128_1]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h127, h3, hc02, hc45, hlam, hphi, ht0b, ht5b, p128_1]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h0, h121, h7, h8, hc45, hlam, hphi, ht01, ht0b, ht5b, p128_1, u1elo0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h4, hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h121, hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h125, hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h4, hc03, hc45, hlam, hphi, ht0b, ht5b, p128_1]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h5, hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h122, hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h126, hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [h127, hlam, p128_0]
                  · have p128_0 := h128c.1
                    have p128_1 := h128c.2.1
                    have p128_2 := h128c.2.2.1
                    have p128_3 := h128c.2.2.2
                    linarith only [hlam, p128_0]
                · linarith only [h0, h127, h5, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h122, h123, h125, h126, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
            · linarith only [h121, h125, h8, hc23, hc34, hlam, hphi]
        · linarith only [h0, h121, h122, h5, h8, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
        · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
          · linarith only [h159, h6, h8, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h161 | h161
            · linarith only [h121, h159, h161, hc13, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h163 | h163
              · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                · rcases h5bigk with h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [hlam, p165_0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p165_1, u1elo0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h0, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p165_1, u1elo0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h0, h121, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p165_1, u1elo0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p165_1, u1elo0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h1, hlam, p165_0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [hlam, p165_0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p165_1, u1elo4]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h121, hlam, p165_1]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h158, hc45, hlam, hphi, ht01, ht0b, ht5b, p165_1, u1elo3]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h3, hlam, p165_1]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h7, hlam, p165_1]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [hlam, p165_0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h161, hlam, p165_1]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h3, hc02, hc45, hlam, hphi, ht0b, ht5b, p165_1]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h4, hlam, p165_0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h4, hc03, hc15, hlam, hphi, ht0b, ht5b, p165_1]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h0, h4, h5, hc25, hlam, hphi, ht01, ht0b, ht5b, p165_1, u1elo0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [hlam, p165_0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h0, h4, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p165_1, u1elo0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h5, hlam, p165_0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h158, hlam, p165_0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h163, hlam, p165_0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [h164, hlam, p165_0]
                  · have p165_0 := h165c.1
                    have p165_1 := h165c.2.1
                    have p165_2 := h165c.2.2.1
                    have p165_3 := h165c.2.2.2
                    linarith only [hlam, p165_0]
                · linarith only [h0, h164, h5, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h158, h163, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
          · linarith only [h0, h158, h193, h5, h6, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h195 | h195
            · linarith only [h121, h193, h195, hc13, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h197 | h197
              · linarith only [h158, h197, h6, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h199 | h199
                · rcases h5bigk with h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p200_1, u1elo0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h193, h197, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p200_1, u1elo0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h158, h199, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p200_1, u1elo0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h158, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p200_1, u1elo0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h1, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h193, h197, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p200_1, u1elo4]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h121, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h158, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h3, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h7, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h195, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h197, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h4, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h4, hc03, hc15, hlam, hphi, ht0b, ht5b, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h193, h197, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p200_1, u1elo0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h158, h193, h4, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p200_1, u1elo0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h5, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h193, h197, h7, hc23, hc45, hlam, hphi, ht34, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h193, h197, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p200_1, u1elo0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h199, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                · linarith only [h0, h199, h5, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
    · rcases m.htr 1 3 5 (by decide) (by decide) with h228 | h228
      · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
        · linarith only [h229, h6, h7, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
          · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
            · rcases m.htr 2 4 5 (by decide) (by decide) with h233 | h233
              · linarith only [h0, h229, h233, h3, h5, h6, h7, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h0, h231, h233, h5, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h228, h231, h232, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · linarith only [h0, h227, h229, h231, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
        · linarith only [h238, h6, h7, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
          · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
            · rcases m.htr 2 4 5 (by decide) (by decide) with h242 | h242
              · linarith only [h0, h238, h242, h3, h5, h6, h7, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h0, h240, h242, h5, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h245 | h245
              · linarith only [h1, h245, h6, h7, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h0, h240, h245, h5, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · linarith only [h0, h227, h228, h240, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h249 | h249
      · linarith only [h227, h249, h6, h7, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h251 | h251
        · linarith only [h251, h6, h7, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h253 | h253
          · linarith only [h0, h227, h253, h3, h5, h6, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h255 | h255
            · linarith only [h249, h253, h255, hc13, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h257 | h257
              · linarith only [h227, h251, h257, h6, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · linarith only [h0, h253, h257, h5, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]

end R2N4
