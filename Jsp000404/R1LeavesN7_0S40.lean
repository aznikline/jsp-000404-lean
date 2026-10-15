import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S38
import Jsp000404.R1LeavesN7_0S39

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x0_x0 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h23348 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h23945 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h23946 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h23947 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 3 4 5 (by decide) (by decide) with h23948 | h23948
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347 h23348 h23945 h23946 h23947 h23948
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347 h23348 h23945 h23946 h23947 h23948

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x0_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h23348 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h23945 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h23946 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h23947 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  linarith only [h0, h19744, h23337, h23339, h23947, h4, hc12, hc23, hlam, hphi]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x0 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h23348 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h23945 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h23946 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 2 4 5 (by decide) (by decide) with h23947 | h23947
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347 h23348 h23945 h23946 h23947
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347 h23348 h23945 h23946 h23947

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h23348 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h23945 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h23946 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  linarith only [h23338, h23946, h4, hlam]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h23348 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h23945 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 2 3 5 (by decide) (by decide) with h23946 | h23946
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347 h23348 h23945 h23946
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347 h23348 h23945 h23946

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h23348 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h23945 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  linarith only [h23337, h23339, h23342, h23348, h23945, h4, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h23348 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 2 3 4 (by decide) (by decide) with h23945 | h23945
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347 h23348 h23945
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347 h23348 h23945

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 1 4 5 (by decide) (by decide) with h23348 | h23348
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347 h23348
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347 h23348

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 1 4 5 (by decide) (by decide) with h24787 | h24787
  · linarith only [h23346, h23347, h24787, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h24789 | h24789
    · rcases m.htr 2 3 5 (by decide) (by decide) with h24790 | h24790
      · rcases m.htr 2 4 5 (by decide) (by decide) with h24791 | h24791
        · rcases m.htr 3 4 5 (by decide) (by decide) with h24792 | h24792
          · linarith only [h23338, h23346, h23347, h24787, h24792, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases h1bigk with h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c | h24794c
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              rcases p24794_3 (m.d 0 1) (by simp) with h24796 | h24796
              · rcases p24794_3 (m.d 1 2) (by simp) with h24797 | h24797
                · linarith only [h24797, hlam, p24794_0]
                · rcases p24794_3 (m.d 1 3) (by simp) with h24799 | h24799
                  · linarith only [h1, h24799, hlam]
                  · linarith only [h23340, h24799, hlam]
              · linarith only [h24796, hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              rcases p24794_3 (m.d 0 1) (by simp) with h24803 | h24803
              · rcases p24794_3 (m.d 1 2) (by simp) with h24804 | h24804
                · linarith only [h0, h24804, hlam]
                · rcases p24794_3 (m.d 1 3) (by simp) with h24806 | h24806
                  · linarith only [h24806, hlam, p24794_0]
                  · rcases p24794_3 (m.d 1 4) (by simp) with h24808 | h24808
                    · linarith only [h2, h24808, hlam]
                    · rcases p24794_3 (m.d 1 5) (by simp) with h24810 | h24810
                      · linarith only [h24810, h3, hlam]
                      · linarith only [h23347, h24810, hlam]
              · linarith only [h24803, hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              rcases p24794_3 (m.d 0 1) (by simp) with h24814 | h24814
              · rcases p24794_3 (m.d 1 2) (by simp) with h24815 | h24815
                · linarith only [h0, h24815, hlam]
                · rcases p24794_3 (m.d 1 3) (by simp) with h24817 | h24817
                  · linarith only [h1, h24817, hlam]
                  · linarith only [h23346, h24817, hlam]
              · linarith only [h24814, hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              rcases p24794_3 (m.d 0 1) (by simp) with h24821 | h24821
              · rcases p24794_3 (m.d 1 2) (by simp) with h24822 | h24822
                · linarith only [h0, h24822, hlam]
                · rcases p24794_3 (m.d 1 3) (by simp) with h24824 | h24824
                  · linarith only [h1, h24824, hlam]
                  · rcases p24794_3 (m.d 1 4) (by simp) with h24826 | h24826
                    · linarith only [h2, h24826, hlam]
                    · rcases p24794_3 (m.d 1 5) (by simp) with h24828 | h24828
                      · linarith only [h24828, hlam, p24794_0]
                      · rcases h1emax with h24830 | h24830 | h24830 | h24830 | h24830
                        · linarith only [h1, h23346, h24830, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h2bigk with h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c | h24832c
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p24832_1]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h4, hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h19744, hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h22010, hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h0, hlam, p24832_1]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h23340, hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h23342, hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h23344, hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            rcases p24832_3 (m.d 0 2) (by simp) with h24843 | h24843
                            · linarith only [h24843, hlam, p24832_0]
                            · rcases p24832_3 (m.d 1 2) (by simp) with h24845 | h24845
                              · linarith only [h23340, h24845, hlam]
                              · rcases p24832_3 (m.d 2 3) (by simp) with h24847 | h24847
                                · rcases p24832_3 (m.d 2 4) (by simp) with h24848 | h24848
                                  · linarith only [h24789, h24848, hlam]
                                  · linarith only [h19744, h24848, hlam]
                                · linarith only [h24847, hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            rcases p24832_3 (m.d 0 2) (by simp) with h24852 | h24852
                            · linarith only [h24852, h4, hlam]
                            · linarith only [h0, h24852, hlam]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p24832_1]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p24832_1]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            rcases p24832_3 (m.d 0 2) (by simp) with h24858 | h24858
                            · linarith only [h24858, hlam, p24832_0]
                            · rcases p24832_3 (m.d 1 2) (by simp) with h24860 | h24860
                              · linarith only [h23342, h24860, hlam]
                              · rcases p24832_3 (m.d 2 3) (by simp) with h24862 | h24862
                                · rcases p24832_3 (m.d 2 4) (by simp) with h24863 | h24863
                                  · rcases p24832_3 (m.d 2 5) (by simp) with h24864 | h24864
                                    · linarith only [h24791, h24864, hlam]
                                    · linarith only [h22010, h24864, hlam]
                                  · linarith only [h24863, hlam, p24832_0]
                                · linarith only [h24862, h4, hlam]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            rcases p24832_3 (m.d 0 2) (by simp) with h24869 | h24869
                            · linarith only [h19744, h24869, hlam]
                            · linarith only [h0, h24869, hlam]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h24789, hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h22010, h23339, h23346, h23347, h24792, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24832_1]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            rcases p24832_3 (m.d 0 2) (by simp) with h24875 | h24875
                            · linarith only [h24875, hlam, p24832_0]
                            · rcases p24832_3 (m.d 1 2) (by simp) with h24877 | h24877
                              · linarith only [h23344, h24877, hlam]
                              · rcases p24832_3 (m.d 2 3) (by simp) with h24879 | h24879
                                · rcases p24832_3 (m.d 2 4) (by simp) with h24880 | h24880
                                  · rcases p24832_3 (m.d 2 5) (by simp) with h24881 | h24881
                                    · rcases h4bigk with h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c | h24882c
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        rcases p24882_3 (m.d 0 4) (by simp) with h24884 | h24884
                                        · rcases p24882_3 (m.d 1 4) (by simp) with h24885 | h24885
                                          · linarith only [h2, h24885, hlam]
                                          · rcases p24882_3 (m.d 2 4) (by simp) with h24887 | h24887
                                            · rcases p24882_3 (m.d 3 4) (by simp) with h24888 | h24888
                                              · linarith only [h23337, h24888, hlam]
                                              · rcases p24882_3 (m.d 4 5) (by simp) with h24890 | h24890
                                                · linarith only [h23339, h24890, hlam]
                                                · linarith only [h24787, h24890, hlam]
                                            · linarith only [h23342, h24887, hlam]
                                        · linarith only [h2, h24884, hlam]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h19744, hlam, p24882_1]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h23339, h23346, h23347, h24792, hlam, p24882_2]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h23346, h23347, h24792, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p24882_1]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h2, hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h23342, hlam, p24882_1]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h23346, h23347, h24792, hc34, hc45, hlam, hphi, p24882_1]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h24787, hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h23338, h23339, h23346, h23347, h24789, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24882_1]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        rcases p24882_3 (m.d 0 4) (by simp) with h24904 | h24904
                                        · linarith only [h19744, h24904, hlam]
                                        · linarith only [h2, h24904, hlam]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h19744, h23339, h23346, h23347, h24792, hlam, p24882_2]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h23346, h23347, h24792, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24882_1]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h23337, hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h23346, hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h24789, hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h24792, hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h23339, hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h19744, h23339, h23342, hc12, hc24, hlam, hphi, p24882_1]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [h24791, hlam, p24882_0]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        rcases p24882_3 (m.d 0 4) (by simp) with h24918 | h24918
                                        · rcases p24882_3 (m.d 1 4) (by simp) with h24919 | h24919
                                          · linarith only [h24787, h24919, hlam]
                                          · linarith only [h23346, h24919, hlam]
                                        · linarith only [h23337, h24918, hlam]
                                      · have p24882_0 := h24882c.1
                                        have p24882_1 := h24882c.2.1
                                        have p24882_2 := h24882c.2.2.1
                                        have p24882_3 := h24882c.2.2.2
                                        linarith only [hlam, p24882_0]
                                    · linarith only [h24881, hlam, p24832_0]
                                  · linarith only [h19744, h24880, hlam]
                                · linarith only [h24879, h4, hlam]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            rcases p24832_3 (m.d 0 2) (by simp) with h24927 | h24927
                            · linarith only [h22010, h24927, hlam]
                            · linarith only [h0, h24927, hlam]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h24790, hlam, p24832_0]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [h24791, hlam, p24832_1]
                          · have p24832_0 := h24832c.1
                            have p24832_1 := h24832c.2.1
                            have p24832_2 := h24832c.2.2.1
                            have p24832_3 := h24832c.2.2.2
                            linarith only [hlam, p24832_0]
                        · rcases h2bigk with h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c | h24933c
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p24933_1]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h4, hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h19744, hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h22010, hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h0, hlam, p24933_1]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h23340, hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h23342, hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h23344, hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            rcases p24933_3 (m.d 0 2) (by simp) with h24944 | h24944
                            · linarith only [h24944, hlam, p24933_0]
                            · rcases p24933_3 (m.d 1 2) (by simp) with h24946 | h24946
                              · linarith only [h23340, h24946, hlam]
                              · rcases p24933_3 (m.d 2 3) (by simp) with h24948 | h24948
                                · rcases p24933_3 (m.d 2 4) (by simp) with h24949 | h24949
                                  · linarith only [h24789, h24949, hlam]
                                  · linarith only [h19744, h24949, hlam]
                                · linarith only [h24948, hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            rcases p24933_3 (m.d 0 2) (by simp) with h24953 | h24953
                            · linarith only [h24953, h4, hlam]
                            · linarith only [h0, h24953, hlam]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p24933_1]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p24933_1]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            rcases p24933_3 (m.d 0 2) (by simp) with h24959 | h24959
                            · linarith only [h24959, hlam, p24933_0]
                            · rcases p24933_3 (m.d 1 2) (by simp) with h24961 | h24961
                              · linarith only [h23342, h24961, hlam]
                              · rcases p24933_3 (m.d 2 3) (by simp) with h24963 | h24963
                                · rcases p24933_3 (m.d 2 4) (by simp) with h24964 | h24964
                                  · rcases p24933_3 (m.d 2 5) (by simp) with h24965 | h24965
                                    · linarith only [h24791, h24965, hlam]
                                    · linarith only [h22010, h24965, hlam]
                                  · linarith only [h24964, hlam, p24933_0]
                                · linarith only [h24963, h4, hlam]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            rcases p24933_3 (m.d 0 2) (by simp) with h24970 | h24970
                            · linarith only [h19744, h24970, hlam]
                            · linarith only [h0, h24970, hlam]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h24789, hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h0, h22010, hc12, hc24, hlam, hphi, p24933_1]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            rcases p24933_3 (m.d 0 2) (by simp) with h24976 | h24976
                            · linarith only [h24976, hlam, p24933_0]
                            · rcases p24933_3 (m.d 1 2) (by simp) with h24978 | h24978
                              · linarith only [h23344, h24978, hlam]
                              · rcases p24933_3 (m.d 2 3) (by simp) with h24980 | h24980
                                · rcases p24933_3 (m.d 2 4) (by simp) with h24981 | h24981
                                  · rcases p24933_3 (m.d 2 5) (by simp) with h24982 | h24982
                                    · rcases h4bigk with h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        rcases p24983_3 (m.d 0 4) (by simp) with h24985 | h24985
                                        · rcases p24983_3 (m.d 1 4) (by simp) with h24986 | h24986
                                          · linarith only [h2, h24986, hlam]
                                          · rcases p24983_3 (m.d 2 4) (by simp) with h24988 | h24988
                                            · rcases p24983_3 (m.d 3 4) (by simp) with h24989 | h24989
                                              · linarith only [h23337, h24989, hlam]
                                              · rcases p24983_3 (m.d 4 5) (by simp) with h24991 | h24991
                                                · linarith only [h23339, h24991, hlam]
                                                · linarith only [h24787, h24991, hlam]
                                            · linarith only [h23342, h24988, hlam]
                                        · linarith only [h2, h24985, hlam]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h19744, hlam, p24983_1]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h23339, h23346, h23347, h24792, hlam, p24983_2]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h19744, h23342, h24787, h24789, hc12, hc23, hlam, hphi, p24983_1]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h2, hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h23342, hlam, p24983_1]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h24787, hc34, hc45, hlam, hphi, p24983_1]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h24787, hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h23338, h23339, h23346, h23347, h24789, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24983_1]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        rcases p24983_3 (m.d 0 4) (by simp) with h25005 | h25005
                                        · linarith only [h19744, h25005, hlam]
                                        · linarith only [h2, h25005, hlam]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h19744, h23339, h23346, h23347, h24792, hlam, p24983_2]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h23346, h23347, h24792, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24983_1]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h23337, hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h23346, hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h24789, hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h24792, hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h23339, hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h19744, h23339, h23342, hc12, hc24, hlam, hphi, p24983_1]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [h24791, hlam, p24983_0]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        rcases p24983_3 (m.d 0 4) (by simp) with h25019 | h25019
                                        · rcases p24983_3 (m.d 1 4) (by simp) with h25020 | h25020
                                          · linarith only [h24787, h25020, hlam]
                                          · linarith only [h23346, h25020, hlam]
                                        · linarith only [h23337, h25019, hlam]
                                      · have p24983_0 := h24983c.1
                                        have p24983_1 := h24983c.2.1
                                        have p24983_2 := h24983c.2.2.1
                                        have p24983_3 := h24983c.2.2.2
                                        linarith only [hlam, p24983_0]
                                    · linarith only [h24982, hlam, p24933_0]
                                  · linarith only [h19744, h24981, hlam]
                                · linarith only [h24980, h4, hlam]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            rcases p24933_3 (m.d 0 2) (by simp) with h25028 | h25028
                            · linarith only [h22010, h25028, hlam]
                            · linarith only [h0, h25028, hlam]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h24790, hlam, p24933_0]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [h24791, hlam, p24933_1]
                          · have p24933_0 := h24933c.1
                            have p24933_1 := h24933c.2.1
                            have p24933_2 := h24933c.2.2.1
                            have p24933_3 := h24933c.2.2.2
                            linarith only [hlam, p24933_0]
                        · rcases h2bigk with h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c | h25034c
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p25034_1]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h4, hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h19744, hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h22010, hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h0, hlam, p25034_1]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h23340, hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h23342, hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h23344, hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            rcases p25034_3 (m.d 0 2) (by simp) with h25045 | h25045
                            · linarith only [h25045, hlam, p25034_0]
                            · rcases p25034_3 (m.d 1 2) (by simp) with h25047 | h25047
                              · linarith only [h23340, h25047, hlam]
                              · rcases p25034_3 (m.d 2 3) (by simp) with h25049 | h25049
                                · rcases p25034_3 (m.d 2 4) (by simp) with h25050 | h25050
                                  · linarith only [h24789, h25050, hlam]
                                  · linarith only [h19744, h25050, hlam]
                                · linarith only [h25049, hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            rcases p25034_3 (m.d 0 2) (by simp) with h25054 | h25054
                            · linarith only [h25054, h4, hlam]
                            · linarith only [h0, h25054, hlam]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p25034_1]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p25034_1]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            rcases p25034_3 (m.d 0 2) (by simp) with h25060 | h25060
                            · linarith only [h25060, hlam, p25034_0]
                            · rcases p25034_3 (m.d 1 2) (by simp) with h25062 | h25062
                              · linarith only [h23342, h25062, hlam]
                              · rcases p25034_3 (m.d 2 3) (by simp) with h25064 | h25064
                                · rcases p25034_3 (m.d 2 4) (by simp) with h25065 | h25065
                                  · rcases p25034_3 (m.d 2 5) (by simp) with h25066 | h25066
                                    · linarith only [h24791, h25066, hlam]
                                    · linarith only [h22010, h25066, hlam]
                                  · linarith only [h25065, hlam, p25034_0]
                                · linarith only [h25064, h4, hlam]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            rcases p25034_3 (m.d 0 2) (by simp) with h25071 | h25071
                            · linarith only [h19744, h25071, hlam]
                            · linarith only [h0, h25071, hlam]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h24789, hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h0, h22010, hc12, hc24, hlam, hphi, p25034_1]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            rcases p25034_3 (m.d 0 2) (by simp) with h25077 | h25077
                            · linarith only [h25077, hlam, p25034_0]
                            · rcases p25034_3 (m.d 1 2) (by simp) with h25079 | h25079
                              · linarith only [h23344, h25079, hlam]
                              · rcases p25034_3 (m.d 2 3) (by simp) with h25081 | h25081
                                · rcases p25034_3 (m.d 2 4) (by simp) with h25082 | h25082
                                  · rcases p25034_3 (m.d 2 5) (by simp) with h25083 | h25083
                                    · rcases h4bigk with h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c | h25084c
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        rcases p25084_3 (m.d 0 4) (by simp) with h25086 | h25086
                                        · rcases p25084_3 (m.d 1 4) (by simp) with h25087 | h25087
                                          · linarith only [h2, h25087, hlam]
                                          · rcases p25084_3 (m.d 2 4) (by simp) with h25089 | h25089
                                            · rcases p25084_3 (m.d 3 4) (by simp) with h25090 | h25090
                                              · linarith only [h23337, h25090, hlam]
                                              · rcases p25084_3 (m.d 4 5) (by simp) with h25092 | h25092
                                                · linarith only [h23339, h25092, hlam]
                                                · linarith only [h24787, h25092, hlam]
                                            · linarith only [h23342, h25089, hlam]
                                        · linarith only [h2, h25086, hlam]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h19744, hlam, p25084_1]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h23339, h23346, h23347, h24792, hlam, p25084_2]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h19744, h23342, h24787, h24789, hc12, hc23, hlam, hphi, p25084_1]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h2, hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h23342, hlam, p25084_1]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h24787, hc34, hc45, hlam, hphi, p25084_1]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h24787, hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h23338, h23339, h23346, h23347, h24789, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p25084_1]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        rcases p25084_3 (m.d 0 4) (by simp) with h25106 | h25106
                                        · linarith only [h19744, h25106, hlam]
                                        · linarith only [h2, h25106, hlam]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h19744, h23339, h23346, h23347, h24792, hlam, p25084_2]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h23346, h23347, h24792, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p25084_1]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h23337, hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h23346, hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h24789, hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h24792, hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h23339, hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h19744, h23339, h23342, hc12, hc24, hlam, hphi, p25084_1]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [h24791, hlam, p25084_0]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        rcases p25084_3 (m.d 0 4) (by simp) with h25120 | h25120
                                        · rcases p25084_3 (m.d 1 4) (by simp) with h25121 | h25121
                                          · linarith only [h24787, h25121, hlam]
                                          · linarith only [h23346, h25121, hlam]
                                        · linarith only [h23337, h25120, hlam]
                                      · have p25084_0 := h25084c.1
                                        have p25084_1 := h25084c.2.1
                                        have p25084_2 := h25084c.2.2.1
                                        have p25084_3 := h25084c.2.2.2
                                        linarith only [hlam, p25084_0]
                                    · linarith only [h25083, hlam, p25034_0]
                                  · linarith only [h19744, h25082, hlam]
                                · linarith only [h25081, h4, hlam]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            rcases p25034_3 (m.d 0 2) (by simp) with h25129 | h25129
                            · linarith only [h22010, h25129, hlam]
                            · linarith only [h0, h25129, hlam]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h24790, hlam, p25034_0]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [h24791, hlam, p25034_1]
                          · have p25034_0 := h25034c.1
                            have p25034_1 := h25034c.2.1
                            have p25034_2 := h25034c.2.2.1
                            have p25034_3 := h25034c.2.2.2
                            linarith only [hlam, p25034_0]
                        · rcases h2bigk with h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c | h25135c
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p25135_1]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h4, hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h19744, hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h22010, hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h0, hlam, p25135_1]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h23340, hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h23342, hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h23344, hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            rcases p25135_3 (m.d 0 2) (by simp) with h25146 | h25146
                            · linarith only [h25146, hlam, p25135_0]
                            · rcases p25135_3 (m.d 1 2) (by simp) with h25148 | h25148
                              · linarith only [h23340, h25148, hlam]
                              · rcases p25135_3 (m.d 2 3) (by simp) with h25150 | h25150
                                · rcases p25135_3 (m.d 2 4) (by simp) with h25151 | h25151
                                  · linarith only [h24789, h25151, hlam]
                                  · linarith only [h19744, h25151, hlam]
                                · linarith only [h25150, hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            rcases p25135_3 (m.d 0 2) (by simp) with h25155 | h25155
                            · linarith only [h25155, h4, hlam]
                            · linarith only [h0, h25155, hlam]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p25135_1]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p25135_1]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            rcases p25135_3 (m.d 0 2) (by simp) with h25161 | h25161
                            · linarith only [h25161, hlam, p25135_0]
                            · rcases p25135_3 (m.d 1 2) (by simp) with h25163 | h25163
                              · linarith only [h23342, h25163, hlam]
                              · rcases p25135_3 (m.d 2 3) (by simp) with h25165 | h25165
                                · rcases p25135_3 (m.d 2 4) (by simp) with h25166 | h25166
                                  · rcases p25135_3 (m.d 2 5) (by simp) with h25167 | h25167
                                    · linarith only [h24791, h25167, hlam]
                                    · linarith only [h22010, h25167, hlam]
                                  · linarith only [h25166, hlam, p25135_0]
                                · linarith only [h25165, h4, hlam]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            rcases p25135_3 (m.d 0 2) (by simp) with h25172 | h25172
                            · linarith only [h19744, h25172, hlam]
                            · linarith only [h0, h25172, hlam]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h24789, hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h0, h22010, hc12, hc24, hlam, hphi, p25135_1]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            rcases p25135_3 (m.d 0 2) (by simp) with h25178 | h25178
                            · linarith only [h25178, hlam, p25135_0]
                            · rcases p25135_3 (m.d 1 2) (by simp) with h25180 | h25180
                              · linarith only [h23344, h25180, hlam]
                              · rcases p25135_3 (m.d 2 3) (by simp) with h25182 | h25182
                                · rcases p25135_3 (m.d 2 4) (by simp) with h25183 | h25183
                                  · rcases p25135_3 (m.d 2 5) (by simp) with h25184 | h25184
                                    · rcases h4bigk with h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c | h25185c
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        rcases p25185_3 (m.d 0 4) (by simp) with h25187 | h25187
                                        · rcases p25185_3 (m.d 1 4) (by simp) with h25188 | h25188
                                          · linarith only [h2, h25188, hlam]
                                          · rcases p25185_3 (m.d 2 4) (by simp) with h25190 | h25190
                                            · rcases p25185_3 (m.d 3 4) (by simp) with h25191 | h25191
                                              · linarith only [h23337, h25191, hlam]
                                              · rcases p25185_3 (m.d 4 5) (by simp) with h25193 | h25193
                                                · linarith only [h23339, h25193, hlam]
                                                · linarith only [h24787, h25193, hlam]
                                            · linarith only [h23342, h25190, hlam]
                                        · linarith only [h2, h25187, hlam]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h19744, hlam, p25185_1]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h23339, h23346, h23347, h24792, hlam, p25185_2]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h19744, h23342, h24787, h24789, hc12, hc23, hlam, hphi, p25185_1]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h2, hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h23342, hlam, p25185_1]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h24787, hc34, hc45, hlam, hphi, p25185_1]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h24787, hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h23338, h23339, h23346, h23347, h24789, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p25185_1]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        rcases p25185_3 (m.d 0 4) (by simp) with h25207 | h25207
                                        · linarith only [h19744, h25207, hlam]
                                        · linarith only [h2, h25207, hlam]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h19744, h23339, h23346, h23347, h24792, hlam, p25185_2]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h23346, h23347, h24792, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p25185_1]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h23337, hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h23346, hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h24789, hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h24792, hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h23339, hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h19744, h23339, h23342, hc12, hc24, hlam, hphi, p25185_1]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [h24791, hlam, p25185_0]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        rcases p25185_3 (m.d 0 4) (by simp) with h25221 | h25221
                                        · rcases p25185_3 (m.d 1 4) (by simp) with h25222 | h25222
                                          · linarith only [h24787, h25222, hlam]
                                          · linarith only [h23346, h25222, hlam]
                                        · linarith only [h23337, h25221, hlam]
                                      · have p25185_0 := h25185c.1
                                        have p25185_1 := h25185c.2.1
                                        have p25185_2 := h25185c.2.2.1
                                        have p25185_3 := h25185c.2.2.2
                                        linarith only [hlam, p25185_0]
                                    · linarith only [h25184, hlam, p25135_0]
                                  · linarith only [h19744, h25183, hlam]
                                · linarith only [h25182, h4, hlam]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            rcases p25135_3 (m.d 0 2) (by simp) with h25230 | h25230
                            · linarith only [h22010, h25230, hlam]
                            · linarith only [h0, h25230, hlam]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h24790, hlam, p25135_0]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [h24791, hlam, p25135_1]
                          · have p25135_0 := h25135c.1
                            have p25135_1 := h25135c.2.1
                            have p25135_2 := h25135c.2.2.1
                            have p25135_3 := h25135c.2.2.2
                            linarith only [hlam, p25135_0]
              · linarith only [h24821, hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h0, hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23340, hlam, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23342, hlam, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23344, hlam, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h1, hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23347, hc12, hc35, hlam, hphi, ht23, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23338, h23342, h23347, h4, hc12, hc23, hlam, hphi, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23347, hlam, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h2, hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23338, h23346, h23347, h4, hc12, hc23, hlam, hphi, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23346, hlam, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h24787, hlam, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h3, hlam, p24794_0]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23338, h23347, h4, hc12, hc23, hlam, hphi, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23338, h23340, h23347, h4, hc12, hc23, hlam, hphi, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [h23337, h23339, h23342, h24787, h4, hc12, hc23, hlam, hphi, p24794_1]
            · have p24794_0 := h24794c.1
              have p24794_1 := h24794c.2.1
              have p24794_2 := h24794c.2.2.1
              have p24794_3 := h24794c.2.2.2
              linarith only [hlam, p24794_0]
        · linarith only [h0, h19744, h23337, h23339, h24791, h4, hc12, hc23, hlam, hphi]
      · linarith only [h23338, h24790, h4, hlam]
    · linarith only [h1, h23337, h23339, h23346, h24787, h24789, h4, hc01, hc15, hlam, hphi, ht0b, ht5b]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 1 3 5 (by decide) (by decide) with h23347 | h23347
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h23347

end R2N4
