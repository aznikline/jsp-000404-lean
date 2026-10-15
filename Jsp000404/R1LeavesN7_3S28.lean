import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S27

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 1 2 5 (by decide) (by decide) with h19118 | h19118
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117 h19118
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117 h19118

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  linarith only [h0, h19111, h19117, hlam]

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 1 2 4 (by decide) (by decide) with h19117 | h19117
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  linarith only [h0, h19110, h19116, hlam]

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 1 2 3 (by decide) (by decide) with h19116 | h19116
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 1 2 3 (by decide) (by decide) with h20362 | h20362
  · rcases m.htr 1 2 4 (by decide) (by decide) with h20363 | h20363
    · rcases m.htr 1 2 5 (by decide) (by decide) with h20364 | h20364
      · rcases m.htr 1 3 4 (by decide) (by decide) with h20365 | h20365
        · rcases m.htr 1 3 5 (by decide) (by decide) with h20366 | h20366
          · rcases m.htr 1 4 5 (by decide) (by decide) with h20367 | h20367
            · rcases m.htr 2 3 4 (by decide) (by decide) with h20368 | h20368
              · rcases m.htr 2 3 5 (by decide) (by decide) with h20369 | h20369
                · rcases m.htr 2 4 5 (by decide) (by decide) with h20370 | h20370
                  · linarith only [h19111, h19115, h20370, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h20372 | h20372
                    · linarith only [h16563, h19110, h19115, h20368, h20372, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c | h20374c
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h0, hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h14799, hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h16563, hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h17994, hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        rcases p20374_3 (m.d 0 1) (by simp) with h20380 | h20380
                        · linarith only [h20380, hlam, p20374_0]
                        · rcases p20374_3 (m.d 1 2) (by simp) with h20382 | h20382
                          · rcases p20374_3 (m.d 1 3) (by simp) with h20383 | h20383
                            · linarith only [h20362, h20383, hlam]
                            · linarith only [h14799, h20383, hlam]
                          · linarith only [h20382, hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h16563, h19115, h20365, h20367, hc01, hc12, hlam, hphi, p20374_1]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h16563, h19115, h20367, hc01, hc12, hlam, hphi, p20374_1]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h16563, h19115, h20367, hc01, hc12, hlam, hphi, p20374_1]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        rcases p20374_3 (m.d 0 1) (by simp) with h20391 | h20391
                        · linarith only [h20391, hlam, p20374_0]
                        · rcases p20374_3 (m.d 1 2) (by simp) with h20393 | h20393
                          · rcases p20374_3 (m.d 1 3) (by simp) with h20394 | h20394
                            · rcases p20374_3 (m.d 1 4) (by simp) with h20395 | h20395
                              · linarith only [h20365, h20395, hlam]
                              · linarith only [h16563, h20395, hlam]
                            · linarith only [h20394, hlam, p20374_0]
                          · linarith only [h0, h20393, hlam]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h20362, hlam, p20374_1]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h16563, h19115, h20367, hc01, hc13, hlam, hphi, p20374_1]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h16563, h19115, h20362, h20367, hc01, hc12, hlam, hphi, p20374_1]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        rcases p20374_3 (m.d 0 1) (by simp) with h20404 | h20404
                        · linarith only [h20404, hlam, p20374_0]
                        · rcases p20374_3 (m.d 1 2) (by simp) with h20406 | h20406
                          · rcases p20374_3 (m.d 1 3) (by simp) with h20407 | h20407
                            · rcases p20374_3 (m.d 1 4) (by simp) with h20408 | h20408
                              · rcases p20374_3 (m.d 1 5) (by simp) with h20409 | h20409
                                · linarith only [h20367, h20409, hlam]
                                · linarith only [h17994, h20409, hlam]
                              · linarith only [h20408, hlam, p20374_0]
                            · linarith only [h14799, h20407, hlam]
                          · linarith only [h0, h20406, hlam]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h20363, hlam, p20374_1]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h20365, hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h16563, h19115, h20367, hc01, hc14, hlam, hphi, p20374_1]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        rcases p20374_3 (m.d 0 1) (by simp) with h20419 | h20419
                        · linarith only [h20419, hlam, p20374_0]
                        · rcases p20374_3 (m.d 1 2) (by simp) with h20421 | h20421
                          · rcases p20374_3 (m.d 1 3) (by simp) with h20422 | h20422
                            · rcases p20374_3 (m.d 1 4) (by simp) with h20423 | h20423
                              · rcases p20374_3 (m.d 1 5) (by simp) with h20424 | h20424
                                · rcases h3bigk with h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c | h20425c
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h14799, hlam, p20425_1]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    rcases p20425_3 (m.d 0 3) (by simp) with h20428 | h20428
                                    · rcases p20425_3 (m.d 1 3) (by simp) with h20429 | h20429
                                      · rcases p20425_3 (m.d 2 3) (by simp) with h20430 | h20430
                                        · linarith only [h19110, h20430, hlam]
                                        · rcases p20425_3 (m.d 3 4) (by simp) with h20432 | h20432
                                          · linarith only [h19113, h20432, hlam]
                                          · rcases p20425_3 (m.d 3 5) (by simp) with h20434 | h20434
                                            · linarith only [h19114, h20434, hlam]
                                            · rcases h5bigk with h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c | h20436c
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [hlam, p20436_0]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h17994, hlam, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h19115, h20362, h20365, h20367, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h19115, h20372, hc34, hc45, hlam, hphi, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h19115, hlam, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h17994, hc01, hc15, hlam, hphi, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [hlam, p20436_0]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                rcases p20436_3 (m.d 0 5) (by simp) with h20444 | h20444
                                                · linarith only [h17994, h20444, hlam]
                                                · linarith only [h19112, h20444, hlam]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                rcases p20436_3 (m.d 0 5) (by simp) with h20447 | h20447
                                                · linarith only [h17994, h20447, hlam]
                                                · linarith only [h19114, h20447, hlam]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h16563, h19115, h20362, h20365, h20367, hc01, hc12, hlam, hphi, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h19112, hlam, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h20364, hlam, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [hlam, p20436_0]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h0, h19112, h20372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h20370, hlam, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h19114, hlam, p20436_0]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h20366, hlam, p20436_0]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h20369, hlam, p20436_0]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [hlam, p20436_0]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h20372, hlam, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h16563, h19115, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h20367, hlam, p20436_0]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h20362, h20365, h20367, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [h20362, h20365, h20367, h20372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20436_1]
                                              · have p20436_0 := h20436c.1
                                                have p20436_1 := h20436c.2.1
                                                have p20436_2 := h20436c.2.2.1
                                                have p20436_3 := h20436c.2.2.2
                                                linarith only [hlam, p20436_0]
                                      · linarith only [h20362, h20429, hlam]
                                    · linarith only [h19110, h20428, hlam]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    rcases p20425_3 (m.d 0 3) (by simp) with h20468 | h20468
                                    · rcases p20425_3 (m.d 1 3) (by simp) with h20469 | h20469
                                      · rcases p20425_3 (m.d 2 3) (by simp) with h20470 | h20470
                                        · linarith only [h19110, h20470, hlam]
                                        · linarith only [h20368, h20470, hlam]
                                      · linarith only [h20365, h20469, hlam]
                                    · linarith only [h20468, hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    rcases p20425_3 (m.d 0 3) (by simp) with h20475 | h20475
                                    · rcases p20425_3 (m.d 1 3) (by simp) with h20476 | h20476
                                      · rcases p20425_3 (m.d 2 3) (by simp) with h20477 | h20477
                                        · linarith only [h19110, h20477, hlam]
                                        · linarith only [h20369, h20477, hlam]
                                      · linarith only [h20366, h20476, hlam]
                                    · linarith only [h20475, hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    rcases p20425_3 (m.d 0 3) (by simp) with h20482 | h20482
                                    · linarith only [h14799, h20482, hlam]
                                    · rcases p20425_3 (m.d 1 3) (by simp) with h20484 | h20484
                                      · rcases p20425_3 (m.d 2 3) (by simp) with h20485 | h20485
                                        · linarith only [h20362, h20485, hlam]
                                        · rcases p20425_3 (m.d 3 4) (by simp) with h20487 | h20487
                                          · linarith only [h20365, h20487, hlam]
                                          · rcases p20425_3 (m.d 3 5) (by simp) with h20489 | h20489
                                            · linarith only [h20366, h20489, hlam]
                                            · rcases h5bigk with h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c | h20491c
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [hlam, p20491_0]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h17994, hlam, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h19114, h20362, h20369, h20372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20425_1, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h19114, h20362, h20372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20425_1, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h19115, hlam, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h17994, h20362, h20365, h20367, hc01, hc12, hlam, hphi, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [hlam, p20491_0]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                rcases p20491_3 (m.d 0 5) (by simp) with h20499 | h20499
                                                · linarith only [h17994, h20499, hlam]
                                                · linarith only [h19112, h20499, hlam]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                rcases p20491_3 (m.d 0 5) (by simp) with h20502 | h20502
                                                · linarith only [h17994, h20502, hlam]
                                                · linarith only [h19114, h20502, hlam]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h16563, h19115, h20362, h20365, h20367, hc01, hc12, hlam, hphi, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h19112, hlam, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h20364, hlam, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [hlam, p20491_0]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h0, h19112, h20372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h20370, hlam, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h19114, hlam, p20491_0]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h20366, hlam, p20491_0]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h20369, hlam, p20491_0]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [hlam, p20491_0]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h20372, hlam, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h17994, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h20367, hlam, p20491_0]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h20362, h20365, h20367, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [h20362, h20365, h20367, h20372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20491_1]
                                              · have p20491_0 := h20491c.1
                                                have p20491_1 := h20491c.2.1
                                                have p20491_2 := h20491c.2.2.1
                                                have p20491_3 := h20491c.2.2.2
                                                linarith only [hlam, p20491_0]
                                      · linarith only [h14799, h20484, hlam]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    rcases p20425_3 (m.d 0 3) (by simp) with h20523 | h20523
                                    · linarith only [h14799, h20523, hlam]
                                    · linarith only [h19110, h20523, hlam]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    rcases p20425_3 (m.d 0 3) (by simp) with h20526 | h20526
                                    · linarith only [h14799, h20526, hlam]
                                    · linarith only [h19113, h20526, hlam]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    rcases p20425_3 (m.d 0 3) (by simp) with h20529 | h20529
                                    · linarith only [h14799, h20529, hlam]
                                    · linarith only [h19114, h20529, hlam]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h19110, hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h20362, hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    rcases p20425_3 (m.d 0 3) (by simp) with h20535 | h20535
                                    · rcases p20425_3 (m.d 1 3) (by simp) with h20536 | h20536
                                      · rcases p20425_3 (m.d 2 3) (by simp) with h20537 | h20537
                                        · rcases p20425_3 (m.d 3 4) (by simp) with h20538 | h20538
                                          · linarith only [h20538, hlam, p20425_0]
                                          · rcases p20425_3 (m.d 3 5) (by simp) with h20540 | h20540
                                            · linarith only [h20369, h20540, hlam]
                                            · linarith only [h20372, h20540, hlam]
                                        · linarith only [h20537, hlam, p20425_0]
                                      · linarith only [h20365, h20536, hlam]
                                    · linarith only [h19113, h20535, hlam]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    rcases p20425_3 (m.d 0 3) (by simp) with h20546 | h20546
                                    · rcases p20425_3 (m.d 1 3) (by simp) with h20547 | h20547
                                      · rcases p20425_3 (m.d 2 3) (by simp) with h20548 | h20548
                                        · rcases p20425_3 (m.d 3 4) (by simp) with h20549 | h20549
                                          · linarith only [h20368, h20549, hlam]
                                          · rcases p20425_3 (m.d 3 5) (by simp) with h20551 | h20551
                                            · linarith only [h20551, hlam, p20425_0]
                                            · rcases h5bigk with h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c | h20553c
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [hlam, p20553_0]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h17994, hlam, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h19115, h20362, h20365, h20367, h20370, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h19115, h20362, h20365, h20367, h20372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h19115, hlam, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h17994, h20362, h20365, h20367, hc01, hc12, hlam, hphi, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [hlam, p20553_0]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                rcases p20553_3 (m.d 0 5) (by simp) with h20561 | h20561
                                                · linarith only [h17994, h20561, hlam]
                                                · linarith only [h19112, h20561, hlam]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                rcases p20553_3 (m.d 0 5) (by simp) with h20564 | h20564
                                                · linarith only [h17994, h20564, hlam]
                                                · linarith only [h19114, h20564, hlam]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h16563, h19115, h20362, h20365, h20367, hc01, hc12, hlam, hphi, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h19112, hlam, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h20364, hlam, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [hlam, p20553_0]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h0, h19112, h20372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h20370, hlam, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h19114, hlam, p20553_0]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h20366, hlam, p20553_0]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h20369, hlam, p20553_0]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [hlam, p20553_0]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h20372, hlam, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h17994, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h20367, hlam, p20553_0]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h20362, h20365, h20367, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [h20362, h20365, h20367, h20372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20553_1]
                                              · have p20553_0 := h20553c.1
                                                have p20553_1 := h20553c.2.1
                                                have p20553_2 := h20553c.2.2.1
                                                have p20553_3 := h20553c.2.2.2
                                                linarith only [hlam, p20553_0]
                                        · linarith only [h20548, hlam, p20425_0]
                                      · linarith only [h20366, h20547, hlam]
                                    · linarith only [h19114, h20546, hlam]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h19113, hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h20365, hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h20368, hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h20372, hlam, p20425_1]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h19114, hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h20366, hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h20369, hlam, p20425_0]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [h0, h19110, h20369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20425_1]
                                  · have p20425_0 := h20425c.1
                                    have p20425_1 := h20425c.2.1
                                    have p20425_2 := h20425c.2.2.1
                                    have p20425_3 := h20425c.2.2.2
                                    linarith only [hlam, p20425_0]
                                · linarith only [h20424, hlam, p20374_0]
                              · linarith only [h16563, h20423, hlam]
                            · linarith only [h14799, h20422, hlam]
                          · linarith only [h0, h20421, hlam]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h20364, hlam, p20374_1]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h20366, hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [h20367, hlam, p20374_0]
                      · have p20374_0 := h20374c.1
                        have p20374_1 := h20374c.2.1
                        have p20374_2 := h20374c.2.2.1
                        have p20374_3 := h20374c.2.2.2
                        linarith only [hlam, p20374_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h20604 | h20604
                  · linarith only [h19111, h19115, h20604, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h20606 | h20606
                    · linarith only [h19114, h19115, h20368, h20369, h20606, hlam]
                    · rcases h1bigk with h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c | h20608c
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h0, hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h14799, hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h16563, hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h17994, hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        rcases p20608_3 (m.d 0 1) (by simp) with h20614 | h20614
                        · linarith only [h20614, hlam, p20608_0]
                        · rcases p20608_3 (m.d 1 2) (by simp) with h20616 | h20616
                          · rcases p20608_3 (m.d 1 3) (by simp) with h20617 | h20617
                            · linarith only [h20362, h20617, hlam]
                            · linarith only [h14799, h20617, hlam]
                          · linarith only [h20616, hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h14799, hc01, hc12, hlam, hphi, p20608_1]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h17994, h19114, h20367, h20368, h20369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20608_1]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h17994, h19114, h20368, h20369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20608_1]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        rcases p20608_3 (m.d 0 1) (by simp) with h20625 | h20625
                        · linarith only [h20625, hlam, p20608_0]
                        · rcases p20608_3 (m.d 1 2) (by simp) with h20627 | h20627
                          · rcases p20608_3 (m.d 1 3) (by simp) with h20628 | h20628
                            · rcases p20608_3 (m.d 1 4) (by simp) with h20629 | h20629
                              · linarith only [h20365, h20629, hlam]
                              · linarith only [h16563, h20629, hlam]
                            · linarith only [h20628, hlam, p20608_0]
                          · linarith only [h0, h20627, hlam]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h20362, hlam, p20608_1]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h19114, h19115, h20367, h20368, h20369, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20608_1]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h19114, h19115, h20362, h20367, h20368, h20369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20608_1]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        rcases p20608_3 (m.d 0 1) (by simp) with h20638 | h20638
                        · linarith only [h20638, hlam, p20608_0]
                        · rcases p20608_3 (m.d 1 2) (by simp) with h20640 | h20640
                          · rcases p20608_3 (m.d 1 3) (by simp) with h20641 | h20641
                            · rcases p20608_3 (m.d 1 4) (by simp) with h20642 | h20642
                              · rcases p20608_3 (m.d 1 5) (by simp) with h20643 | h20643
                                · linarith only [h20367, h20643, hlam]
                                · linarith only [h17994, h20643, hlam]
                              · linarith only [h20642, hlam, p20608_0]
                            · linarith only [h14799, h20641, hlam]
                          · linarith only [h0, h20640, hlam]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h20363, hlam, p20608_1]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h20365, hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h19114, h19115, h20367, h20368, h20369, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20608_1]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        rcases p20608_3 (m.d 0 1) (by simp) with h20653 | h20653
                        · linarith only [h20653, hlam, p20608_0]
                        · rcases p20608_3 (m.d 1 2) (by simp) with h20655 | h20655
                          · rcases p20608_3 (m.d 1 3) (by simp) with h20656 | h20656
                            · rcases p20608_3 (m.d 1 4) (by simp) with h20657 | h20657
                              · rcases p20608_3 (m.d 1 5) (by simp) with h20658 | h20658
                                · rcases h3bigk with h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h14799, hlam, p20659_1]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    rcases p20659_3 (m.d 0 3) (by simp) with h20662 | h20662
                                    · rcases p20659_3 (m.d 1 3) (by simp) with h20663 | h20663
                                      · rcases p20659_3 (m.d 2 3) (by simp) with h20664 | h20664
                                        · linarith only [h19110, h20664, hlam]
                                        · rcases p20659_3 (m.d 3 4) (by simp) with h20666 | h20666
                                          · linarith only [h19113, h20666, hlam]
                                          · rcases p20659_3 (m.d 3 5) (by simp) with h20668 | h20668
                                            · linarith only [h19114, h20668, hlam]
                                            · linarith only [h20369, h20668, hlam]
                                      · linarith only [h20362, h20663, hlam]
                                    · linarith only [h19110, h20662, hlam]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h19114, h20368, h20369, hlam, p20659_2]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h20368, h20369, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p20659_1]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h19114, h20362, h20368, h20369, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20659_1]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    rcases p20659_3 (m.d 0 3) (by simp) with h20677 | h20677
                                    · linarith only [h14799, h20677, hlam]
                                    · linarith only [h19110, h20677, hlam]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h14799, h19114, h20368, h20369, hlam, p20659_2]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h20368, h20369, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20659_1]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h19110, hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h20362, hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h19114, h20369, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p20659_1]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h20369, hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h19113, hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h20365, hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h20368, hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h20606, hlam, p20659_1]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h19114, hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h20366, hlam, p20659_0]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [h19114, h19115, h20362, h20365, h20367, h20368, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20659_1]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    rcases p20659_3 (m.d 0 3) (by simp) with h20695 | h20695
                                    · rcases p20659_3 (m.d 1 3) (by simp) with h20696 | h20696
                                      · rcases p20659_3 (m.d 2 3) (by simp) with h20697 | h20697
                                        · linarith only [h20369, h20697, hlam]
                                        · linarith only [h20368, h20697, hlam]
                                      · linarith only [h20365, h20696, hlam]
                                    · linarith only [h19113, h20695, hlam]
                                  · have p20659_0 := h20659c.1
                                    have p20659_1 := h20659c.2.1
                                    have p20659_2 := h20659c.2.2.1
                                    have p20659_3 := h20659c.2.2.2
                                    linarith only [hlam, p20659_0]
                                · linarith only [h20658, hlam, p20608_0]
                              · linarith only [h16563, h20657, hlam]
                            · linarith only [h14799, h20656, hlam]
                          · linarith only [h0, h20655, hlam]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h20364, hlam, p20608_1]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h20366, hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [h20367, hlam, p20608_0]
                      · have p20608_0 := h20608c.1
                        have p20608_1 := h20608c.2.1
                        have p20608_2 := h20608c.2.2.1
                        have p20608_3 := h20608c.2.2.2
                        linarith only [hlam, p20608_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h20711 | h20711
                · linarith only [h19113, h19115, h20362, h20365, h20367, h20368, h20711, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h20713 | h20713
                  · linarith only [h19113, h19115, h20368, h20713, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h20715 | h20715
                    · linarith only [h19113, h19115, h20715, hlam]
                    · rcases h1bigk with h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h0, hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h14799, hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h16563, hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h17994, hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        rcases p20717_3 (m.d 0 1) (by simp) with h20723 | h20723
                        · linarith only [h20723, hlam, p20717_0]
                        · rcases p20717_3 (m.d 1 2) (by simp) with h20725 | h20725
                          · rcases p20717_3 (m.d 1 3) (by simp) with h20726 | h20726
                            · linarith only [h20362, h20726, hlam]
                            · linarith only [h14799, h20726, hlam]
                          · linarith only [h20725, hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h19115, h20365, h20367, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p20717_1]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h19113, h19115, h20367, h20368, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20717_1]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h17994, hc01, hc12, hlam, hphi, p20717_1]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        rcases p20717_3 (m.d 0 1) (by simp) with h20734 | h20734
                        · linarith only [h20734, hlam, p20717_0]
                        · rcases p20717_3 (m.d 1 2) (by simp) with h20736 | h20736
                          · rcases p20717_3 (m.d 1 3) (by simp) with h20737 | h20737
                            · rcases p20717_3 (m.d 1 4) (by simp) with h20738 | h20738
                              · linarith only [h20365, h20738, hlam]
                              · linarith only [h16563, h20738, hlam]
                            · linarith only [h20737, hlam, p20717_0]
                          · linarith only [h0, h20736, hlam]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h20362, hlam, p20717_1]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h19113, h19115, h20367, h20368, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20717_1]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h19113, h19115, h20362, h20367, h20368, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20717_1]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        rcases p20717_3 (m.d 0 1) (by simp) with h20747 | h20747
                        · linarith only [h20747, hlam, p20717_0]
                        · rcases p20717_3 (m.d 1 2) (by simp) with h20749 | h20749
                          · rcases p20717_3 (m.d 1 3) (by simp) with h20750 | h20750
                            · rcases p20717_3 (m.d 1 4) (by simp) with h20751 | h20751
                              · rcases p20717_3 (m.d 1 5) (by simp) with h20752 | h20752
                                · linarith only [h20367, h20752, hlam]
                                · linarith only [h17994, h20752, hlam]
                              · linarith only [h20751, hlam, p20717_0]
                            · linarith only [h14799, h20750, hlam]
                          · linarith only [h0, h20749, hlam]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h20363, hlam, p20717_1]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h20365, hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h19113, h19115, h20367, h20368, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20717_1]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        rcases p20717_3 (m.d 0 1) (by simp) with h20762 | h20762
                        · linarith only [h20762, hlam, p20717_0]
                        · rcases p20717_3 (m.d 1 2) (by simp) with h20764 | h20764
                          · rcases p20717_3 (m.d 1 3) (by simp) with h20765 | h20765
                            · rcases p20717_3 (m.d 1 4) (by simp) with h20766 | h20766
                              · rcases p20717_3 (m.d 1 5) (by simp) with h20767 | h20767
                                · rcases h3bigk with h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c | h20768c
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h14799, hlam, p20768_1]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    rcases p20768_3 (m.d 0 3) (by simp) with h20771 | h20771
                                    · rcases p20768_3 (m.d 1 3) (by simp) with h20772 | h20772
                                      · rcases p20768_3 (m.d 2 3) (by simp) with h20773 | h20773
                                        · linarith only [h19110, h20773, hlam]
                                        · rcases p20768_3 (m.d 3 4) (by simp) with h20775 | h20775
                                          · linarith only [h19113, h20775, hlam]
                                          · linarith only [h20368, h20775, hlam]
                                      · linarith only [h20362, h20772, hlam]
                                    · linarith only [h19110, h20771, hlam]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    rcases p20768_3 (m.d 0 3) (by simp) with h20780 | h20780
                                    · rcases p20768_3 (m.d 1 3) (by simp) with h20781 | h20781
                                      · rcases p20768_3 (m.d 2 3) (by simp) with h20782 | h20782
                                        · linarith only [h19110, h20782, hlam]
                                        · rcases p20768_3 (m.d 3 4) (by simp) with h20784 | h20784
                                          · linarith only [h20784, hlam, p20768_0]
                                          · rcases p20768_3 (m.d 3 5) (by simp) with h20786 | h20786
                                            · linarith only [h19114, h20786, hlam]
                                            · linarith only [h20715, h20786, hlam]
                                      · linarith only [h20365, h20781, hlam]
                                    · linarith only [h20780, hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    rcases p20768_3 (m.d 0 3) (by simp) with h20791 | h20791
                                    · rcases p20768_3 (m.d 1 3) (by simp) with h20792 | h20792
                                      · rcases p20768_3 (m.d 2 3) (by simp) with h20793 | h20793
                                        · linarith only [h19110, h20793, hlam]
                                        · rcases p20768_3 (m.d 3 4) (by simp) with h20795 | h20795
                                          · linarith only [h19113, h20795, hlam]
                                          · rcases p20768_3 (m.d 3 5) (by simp) with h20797 | h20797
                                            · linarith only [h20797, hlam, p20768_0]
                                            · rcases h5bigk with h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c | h20799c
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [hlam, p20799_0]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h17994, hlam, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h19115, h20713, hc24, hc45, hlam, hphi, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h19115, h20368, h20715, hc23, hc45, hlam, hphi, ht34, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h19115, hlam, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h17994, hc01, hc15, hlam, hphi, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [hlam, p20799_0]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                rcases p20799_3 (m.d 0 5) (by simp) with h20807 | h20807
                                                · linarith only [h17994, h20807, hlam]
                                                · linarith only [h19112, h20807, hlam]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h20362, h20365, h20367, h20368, h20715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h19113, h19115, h20362, h20365, h20367, h20368, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h19112, hlam, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h20364, hlam, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [hlam, p20799_0]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h20711, hlam, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h20713, hlam, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h19114, hlam, p20799_0]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h20366, hlam, p20799_0]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h20368, h20713, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20768_1, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [hlam, p20799_0]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h20715, hlam, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h17994, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h20367, hlam, p20799_0]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h20362, h20365, h20367, h20368, h20713, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [h20362, h20365, h20367, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p20799_1]
                                              · have p20799_0 := h20799c.1
                                                have p20799_1 := h20799c.2.1
                                                have p20799_2 := h20799c.2.2.1
                                                have p20799_3 := h20799c.2.2.2
                                                linarith only [hlam, p20799_0]
                                      · linarith only [h20366, h20792, hlam]
                                    · linarith only [h20791, hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h19113, h20362, h20368, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20768_1]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h19113, h19115, h20365, h20367, h20368, hlam, p20768_2]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    rcases p20768_3 (m.d 0 3) (by simp) with h20832 | h20832
                                    · linarith only [h14799, h20832, hlam]
                                    · linarith only [h19113, h20832, hlam]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    rcases p20768_3 (m.d 0 3) (by simp) with h20835 | h20835
                                    · linarith only [h14799, h20835, hlam]
                                    · linarith only [h19114, h20835, hlam]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h19110, hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h20362, hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h20368, hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h20711, hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h19113, hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h20365, hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h19113, h19115, h20362, h20365, h20367, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20768_1]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h20715, hlam, p20768_1]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h19114, hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h20366, hlam, p20768_0]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    rcases p20768_3 (m.d 0 3) (by simp) with h20850 | h20850
                                    · rcases p20768_3 (m.d 1 3) (by simp) with h20851 | h20851
                                      · rcases p20768_3 (m.d 2 3) (by simp) with h20852 | h20852
                                        · linarith only [h20852, hlam, p20768_0]
                                        · rcases p20768_3 (m.d 3 4) (by simp) with h20854 | h20854
                                          · linarith only [h20715, h20854, hlam]
                                          · linarith only [h20368, h20854, hlam]
                                      · linarith only [h20362, h20851, hlam]
                                    · linarith only [h19110, h20850, hlam]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [h19114, h20368, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20768_1]
                                  · have p20768_0 := h20768c.1
                                    have p20768_1 := h20768c.2.1
                                    have p20768_2 := h20768c.2.2.1
                                    have p20768_3 := h20768c.2.2.2
                                    linarith only [hlam, p20768_0]
                                · linarith only [h20767, hlam, p20717_0]
                              · linarith only [h16563, h20766, hlam]
                            · linarith only [h14799, h20765, hlam]
                          · linarith only [h0, h20764, hlam]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h20364, hlam, p20717_1]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h20366, hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [h20367, hlam, p20717_0]
                      · have p20717_0 := h20717c.1
                        have p20717_1 := h20717c.2.1
                        have p20717_2 := h20717c.2.2.1
                        have p20717_3 := h20717c.2.2.2
                        linarith only [hlam, p20717_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h20869 | h20869
              · rcases m.htr 2 3 5 (by decide) (by decide) with h20870 | h20870
                · rcases m.htr 2 4 5 (by decide) (by decide) with h20871 | h20871
                  · linarith only [h0, h17994, h19111, h20367, h20871, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h20873 | h20873
                    · linarith only [h16563, h20367, h20869, h20873, hc01, hc23, hlam, hphi, ht12]
                    · rcases h1bigk with h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c | h20875c
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h0, hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h14799, hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h16563, hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h17994, hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        rcases p20875_3 (m.d 0 1) (by simp) with h20881 | h20881
                        · linarith only [h20881, hlam, p20875_0]
                        · rcases p20875_3 (m.d 1 2) (by simp) with h20883 | h20883
                          · rcases p20875_3 (m.d 1 3) (by simp) with h20884 | h20884
                            · linarith only [h20362, h20884, hlam]
                            · linarith only [h14799, h20884, hlam]
                          · linarith only [h20883, hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h14799, hc01, hc12, hlam, hphi, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h16563, hc01, hc12, hlam, hphi, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h17994, hc01, hc12, hlam, hphi, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        rcases p20875_3 (m.d 0 1) (by simp) with h20892 | h20892
                        · linarith only [h20892, hlam, p20875_0]
                        · rcases p20875_3 (m.d 1 2) (by simp) with h20894 | h20894
                          · rcases p20875_3 (m.d 1 3) (by simp) with h20895 | h20895
                            · rcases p20875_3 (m.d 1 4) (by simp) with h20896 | h20896
                              · linarith only [h20365, h20896, hlam]
                              · linarith only [h16563, h20896, hlam]
                            · linarith only [h20895, hlam, p20875_0]
                          · linarith only [h0, h20894, hlam]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h20362, hlam, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h16563, hc01, hc13, hlam, hphi, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h17994, h20362, hc01, hc12, hlam, hphi, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h20367, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h20363, hlam, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h20365, hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h20367, hlam, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        rcases p20875_3 (m.d 0 1) (by simp) with h20910 | h20910
                        · linarith only [h20910, hlam, p20875_0]
                        · rcases p20875_3 (m.d 1 2) (by simp) with h20912 | h20912
                          · rcases p20875_3 (m.d 1 3) (by simp) with h20913 | h20913
                            · rcases p20875_3 (m.d 1 4) (by simp) with h20914 | h20914
                              · linarith only [h20367, h20914, hlam]
                              · linarith only [h16563, h20914, hlam]
                            · linarith only [h14799, h20913, hlam]
                          · linarith only [h0, h20912, hlam]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h20364, hlam, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h20366, hlam, p20875_0]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [h16563, hc01, hc15, hlam, hphi, p20875_1]
                      · have p20875_0 := h20875c.1
                        have p20875_1 := h20875c.2.1
                        have p20875_2 := h20875c.2.2.1
                        have p20875_3 := h20875c.2.2.2
                        linarith only [hlam, p20875_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h20923 | h20923
                  · linarith only [h17994, h20367, h20869, h20870, h20923, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h20925 | h20925
                    · linarith only [h16563, h19114, h20367, h20869, h20870, h20925, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c | h20927c
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h0, hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h14799, hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h16563, hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h17994, hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        rcases p20927_3 (m.d 0 1) (by simp) with h20933 | h20933
                        · linarith only [h20933, hlam, p20927_0]
                        · rcases p20927_3 (m.d 1 2) (by simp) with h20935 | h20935
                          · rcases p20927_3 (m.d 1 3) (by simp) with h20936 | h20936
                            · linarith only [h20362, h20936, hlam]
                            · linarith only [h14799, h20936, hlam]
                          · linarith only [h20935, hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h14799, hc01, hc12, hlam, hphi, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h16563, hc01, hc12, hlam, hphi, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h17994, hc01, hc12, hlam, hphi, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        rcases p20927_3 (m.d 0 1) (by simp) with h20944 | h20944
                        · linarith only [h20944, hlam, p20927_0]
                        · rcases p20927_3 (m.d 1 2) (by simp) with h20946 | h20946
                          · rcases p20927_3 (m.d 1 3) (by simp) with h20947 | h20947
                            · rcases p20927_3 (m.d 1 4) (by simp) with h20948 | h20948
                              · linarith only [h20365, h20948, hlam]
                              · linarith only [h16563, h20948, hlam]
                            · linarith only [h20947, hlam, p20927_0]
                          · linarith only [h0, h20946, hlam]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h20362, hlam, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h16563, hc01, hc13, hlam, hphi, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h17994, h19114, h20362, h20869, h20870, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h20367, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h20363, hlam, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h20365, hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h20367, hlam, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        rcases p20927_3 (m.d 0 1) (by simp) with h20962 | h20962
                        · linarith only [h20962, hlam, p20927_0]
                        · rcases p20927_3 (m.d 1 2) (by simp) with h20964 | h20964
                          · rcases p20927_3 (m.d 1 3) (by simp) with h20965 | h20965
                            · rcases p20927_3 (m.d 1 4) (by simp) with h20966 | h20966
                              · linarith only [h20367, h20966, hlam]
                              · linarith only [h16563, h20966, hlam]
                            · linarith only [h14799, h20965, hlam]
                          · linarith only [h0, h20964, hlam]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h20364, hlam, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h20366, hlam, p20927_0]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [h16563, hc01, hc15, hlam, hphi, p20927_1]
                      · have p20927_0 := h20927c.1
                        have p20927_1 := h20927c.2.1
                        have p20927_2 := h20927c.2.2.1
                        have p20927_3 := h20927c.2.2.2
                        linarith only [hlam, p20927_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h20975 | h20975
                · rcases m.htr 2 4 5 (by decide) (by decide) with h20976 | h20976
                  · linarith only [h0, h17994, h19111, h20367, h20976, hc01, hc12, hlam, hphi]
                  · linarith only [h20869, h20975, h20976, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h20979 | h20979
                  · linarith only [h16563, h20367, h20979, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h20981 | h20981
                    · linarith only [h16563, h19113, h20367, h20981, hlam]
                    · rcases h1bigk with h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c | h20983c
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h0, hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h14799, hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h16563, hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h17994, hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        rcases p20983_3 (m.d 0 1) (by simp) with h20989 | h20989
                        · linarith only [h20989, hlam, p20983_0]
                        · rcases p20983_3 (m.d 1 2) (by simp) with h20991 | h20991
                          · rcases p20983_3 (m.d 1 3) (by simp) with h20992 | h20992
                            · linarith only [h20362, h20992, hlam]
                            · linarith only [h14799, h20992, hlam]
                          · linarith only [h20991, hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h14799, hc01, hc12, hlam, hphi, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h16563, hc01, hc12, hlam, hphi, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h17994, hc01, hc12, hlam, hphi, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        rcases p20983_3 (m.d 0 1) (by simp) with h21000 | h21000
                        · linarith only [h21000, hlam, p20983_0]
                        · rcases p20983_3 (m.d 1 2) (by simp) with h21002 | h21002
                          · rcases p20983_3 (m.d 1 3) (by simp) with h21003 | h21003
                            · rcases p20983_3 (m.d 1 4) (by simp) with h21004 | h21004
                              · linarith only [h20365, h21004, hlam]
                              · linarith only [h16563, h21004, hlam]
                            · linarith only [h21003, hlam, p20983_0]
                          · linarith only [h0, h21002, hlam]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h20362, hlam, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h16563, hc01, hc13, hlam, hphi, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h17994, h20362, hc01, hc12, hlam, hphi, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h20367, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h20363, hlam, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h20365, hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h20367, hlam, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        rcases p20983_3 (m.d 0 1) (by simp) with h21018 | h21018
                        · linarith only [h21018, hlam, p20983_0]
                        · rcases p20983_3 (m.d 1 2) (by simp) with h21020 | h21020
                          · rcases p20983_3 (m.d 1 3) (by simp) with h21021 | h21021
                            · rcases p20983_3 (m.d 1 4) (by simp) with h21022 | h21022
                              · linarith only [h20367, h21022, hlam]
                              · linarith only [h16563, h21022, hlam]
                            · linarith only [h14799, h21021, hlam]
                          · linarith only [h0, h21020, hlam]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h20364, hlam, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h20366, hlam, p20983_0]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [h16563, hc01, hc15, hlam, hphi, p20983_1]
                      · have p20983_0 := h20983c.1
                        have p20983_1 := h20983c.2.1
                        have p20983_2 := h20983c.2.2.1
                        have p20983_3 := h20983c.2.2.2
                        linarith only [hlam, p20983_0]
          · linarith only [h14799, h19114, h20366, hlam]
        · linarith only [h14799, h19113, h20365, hlam]
      · linarith only [h0, h19112, h20364, hlam]
    · linarith only [h0, h19111, h20363, hlam]
  · linarith only [h0, h19110, h20362, hlam]

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 0 4 5 (by decide) (by decide) with h19115 | h19115
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115

end R2N4
