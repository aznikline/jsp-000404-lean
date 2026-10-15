import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S7
import Jsp000404.R1LeavesN7_0S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x1 (m : N7Model)
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  linarith only [h1, h10, h4130, h4717, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0 (m : N7Model)
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  rcases m.htr 2 3 5 (by decide) (by decide) with h4717 | h4717
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x1 (m : N7Model)
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  linarith only [h10, h4129, h4716, hlam]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1 (m : N7Model)
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  rcases m.htr 2 3 4 (by decide) (by decide) with h4716 | h4716
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0 (m : N7Model)
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  rcases m.htr 1 4 5 (by decide) (by decide) with h4131 | h4131
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x1 (m : N7Model)
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  rcases m.htr 1 4 5 (by decide) (by decide) with h6437 | h6437
  · linarith only [h4129, h4130, h6437, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h6439 | h6439
    · rcases m.htr 2 3 5 (by decide) (by decide) with h6440 | h6440
      · linarith only [h0, h4, h4129, h4130, h6440, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h6442 | h6442
        · linarith only [h6437, h6439, h6440, h6442, h8, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h6444 | h6444
          · linarith only [h1, h4129, h6442, h6444, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases h1bigk with h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c | h6446c
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h0, h10, h4, h6440, h6444, h7, h9, hlam, p6446_2]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              rcases p6446_3 (m.d 0 1) (by simp) with h6449 | h6449
              · rcases p6446_3 (m.d 1 2) (by simp) with h6450 | h6450
                · linarith only [h0, h6450, hlam]
                · rcases p6446_3 (m.d 1 3) (by simp) with h6452 | h6452
                  · linarith only [h6452, hlam, p6446_0]
                  · rcases p6446_3 (m.d 1 4) (by simp) with h6454 | h6454
                    · linarith only [h2, h6454, hlam]
                    · rcases p6446_3 (m.d 1 5) (by simp) with h6456 | h6456
                      · linarith only [h3, h6456, hlam]
                      · linarith only [h4130, h6456, hlam]
              · linarith only [h6449, hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              rcases p6446_3 (m.d 0 1) (by simp) with h6460 | h6460
              · rcases p6446_3 (m.d 1 2) (by simp) with h6461 | h6461
                · linarith only [h0, h6461, hlam]
                · rcases p6446_3 (m.d 1 3) (by simp) with h6463 | h6463
                  · linarith only [h1, h6463, hlam]
                  · linarith only [h4129, h6463, hlam]
              · linarith only [h6460, hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              rcases p6446_3 (m.d 0 1) (by simp) with h6467 | h6467
              · rcases p6446_3 (m.d 1 2) (by simp) with h6468 | h6468
                · linarith only [h0, h6468, hlam]
                · rcases p6446_3 (m.d 1 3) (by simp) with h6470 | h6470
                  · linarith only [h1, h6470, hlam]
                  · rcases p6446_3 (m.d 1 4) (by simp) with h6472 | h6472
                    · linarith only [h2, h6472, hlam]
                    · rcases p6446_3 (m.d 1 5) (by simp) with h6474 | h6474
                      · linarith only [h6474, hlam, p6446_0]
                      · rcases h1emax with h6476 | h6476 | h6476 | h6476 | h6476
                        · linarith only [h0, h3576, h4, h6439, h6440, h6444, h6476, h7, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h2bigk with h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c | h6478c
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h3576, h4, h6439, h6440, h6444, h7, h9, hlam, p6478_2]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            rcases p6478_3 (m.d 0 2) (by simp) with h6481 | h6481
                            · rcases p6478_3 (m.d 1 2) (by simp) with h6482 | h6482
                              · linarith only [h0, h6482, hlam]
                              · rcases p6478_3 (m.d 2 3) (by simp) with h6484 | h6484
                                · linarith only [h6484, hlam, p6478_0]
                                · rcases p6478_3 (m.d 2 4) (by simp) with h6486 | h6486
                                  · linarith only [h5, h6486, hlam]
                                  · rcases p6478_3 (m.d 2 5) (by simp) with h6488 | h6488
                                    · linarith only [h6, h6488, hlam]
                                    · linarith only [h6440, h6488, hlam]
                            · linarith only [h6481, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            rcases p6478_3 (m.d 0 2) (by simp) with h6492 | h6492
                            · rcases p6478_3 (m.d 1 2) (by simp) with h6493 | h6493
                              · linarith only [h0, h6493, hlam]
                              · rcases p6478_3 (m.d 2 3) (by simp) with h6495 | h6495
                                · linarith only [h4, h6495, hlam]
                                · linarith only [h6439, h6495, hlam]
                            · linarith only [h6492, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            rcases p6478_3 (m.d 0 2) (by simp) with h6499 | h6499
                            · rcases p6478_3 (m.d 1 2) (by simp) with h6500 | h6500
                              · linarith only [h0, h6500, hlam]
                              · rcases p6478_3 (m.d 2 3) (by simp) with h6502 | h6502
                                · linarith only [h4, h6502, hlam]
                                · rcases p6478_3 (m.d 2 4) (by simp) with h6504 | h6504
                                  · linarith only [h5, h6504, hlam]
                                  · rcases p6478_3 (m.d 2 5) (by simp) with h6506 | h6506
                                    · linarith only [h6506, hlam, p6478_0]
                                    · rcases h4bigk with h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c | h6508c
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        rcases p6508_3 (m.d 0 4) (by simp) with h6510 | h6510
                                        · rcases p6508_3 (m.d 1 4) (by simp) with h6511 | h6511
                                          · linarith only [h2, h6511, hlam]
                                          · rcases p6508_3 (m.d 2 4) (by simp) with h6513 | h6513
                                            · linarith only [h5, h6513, hlam]
                                            · linarith only [h3576, h6513, hlam]
                                        · linarith only [h2, h6510, hlam]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        rcases p6508_3 (m.d 0 4) (by simp) with h6517 | h6517
                                        · rcases p6508_3 (m.d 1 4) (by simp) with h6518 | h6518
                                          · linarith only [h2, h6518, hlam]
                                          · rcases p6508_3 (m.d 2 4) (by simp) with h6520 | h6520
                                            · linarith only [h5, h6520, hlam]
                                            · rcases p6508_3 (m.d 3 4) (by simp) with h6522 | h6522
                                              · linarith only [h6522, h7, hlam]
                                              · rcases p6508_3 (m.d 4 5) (by simp) with h6524 | h6524
                                                · linarith only [h6524, h9, hlam]
                                                · linarith only [h6442, h6524, hlam]
                                        · linarith only [h5, h6517, hlam]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h10, h4129, h6440, h6444, h9, hlam, p6508_2]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h0, h3576, h4, h6439, h6440, h6444, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6508_1]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h2, hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h3576, hlam, p6508_1]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h3576, h6439, h6440, h6444, hc34, hc45, hlam, hphi, p6508_1]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h6437, hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h5, hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h6439, h6440, h6444, hc14, hc45, hlam, hphi, p6508_1]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h0, h4, h6439, h6440, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6508_1]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h6442, hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h7, hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h4129, hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h6439, hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h6444, hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h9, hlam, p6508_0]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        rcases p6508_3 (m.d 0 4) (by simp) with h6546 | h6546
                                        · rcases p6508_3 (m.d 1 4) (by simp) with h6547 | h6547
                                          · linarith only [h6547, hlam, p6508_0]
                                          · rcases p6508_3 (m.d 2 4) (by simp) with h6549 | h6549
                                            · linarith only [h6442, h6549, hlam]
                                            · linarith only [h3576, h6549, hlam]
                                        · linarith only [h2, h6546, hlam]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [h0, h3576, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6508_1]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        rcases p6508_3 (m.d 0 4) (by simp) with h6554 | h6554
                                        · rcases p6508_3 (m.d 1 4) (by simp) with h6555 | h6555
                                          · linarith only [h6437, h6555, hlam]
                                          · linarith only [h4129, h6555, hlam]
                                        · linarith only [h6554, h7, hlam]
                                      · have p6508_0 := h6508c.1
                                        have p6508_1 := h6508c.2.1
                                        have p6508_2 := h6508c.2.2.1
                                        have p6508_3 := h6508c.2.2.2
                                        linarith only [hlam, p6508_0]
                            · linarith only [h6499, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h0, hlam, p6478_1]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h10, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h3576, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h4058, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h4, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h0, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6478_1]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h0, h3576, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6478_1]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h6440, hlam, p6478_1]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h5, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h0, h4, h6439, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6478_1]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h6439, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h6442, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h6, hlam, p6478_0]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            rcases p6478_3 (m.d 0 2) (by simp) with h6577 | h6577
                            · rcases p6478_3 (m.d 1 2) (by simp) with h6578 | h6578
                              · linarith only [h6578, hlam, p6478_0]
                              · rcases p6478_3 (m.d 2 3) (by simp) with h6580 | h6580
                                · linarith only [h6440, h6580, hlam]
                                · linarith only [h10, h6580, hlam]
                            · linarith only [h0, h6577, hlam]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h0, h10, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6478_1]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [h0, h3576, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6478_1]
                          · have p6478_0 := h6478c.1
                            have p6478_1 := h6478c.2.1
                            have p6478_2 := h6478c.2.2.1
                            have p6478_3 := h6478c.2.2.2
                            linarith only [hlam, p6478_0]
                        · rcases h2bigk with h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c | h6587c
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h3576, h4, h6439, h6440, h6444, h7, h9, hlam, p6587_2]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            rcases p6587_3 (m.d 0 2) (by simp) with h6590 | h6590
                            · rcases p6587_3 (m.d 1 2) (by simp) with h6591 | h6591
                              · linarith only [h0, h6591, hlam]
                              · rcases p6587_3 (m.d 2 3) (by simp) with h6593 | h6593
                                · linarith only [h6593, hlam, p6587_0]
                                · rcases p6587_3 (m.d 2 4) (by simp) with h6595 | h6595
                                  · linarith only [h5, h6595, hlam]
                                  · rcases p6587_3 (m.d 2 5) (by simp) with h6597 | h6597
                                    · linarith only [h6, h6597, hlam]
                                    · linarith only [h6440, h6597, hlam]
                            · linarith only [h6590, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            rcases p6587_3 (m.d 0 2) (by simp) with h6601 | h6601
                            · rcases p6587_3 (m.d 1 2) (by simp) with h6602 | h6602
                              · linarith only [h0, h6602, hlam]
                              · rcases p6587_3 (m.d 2 3) (by simp) with h6604 | h6604
                                · linarith only [h4, h6604, hlam]
                                · linarith only [h6439, h6604, hlam]
                            · linarith only [h6601, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            rcases p6587_3 (m.d 0 2) (by simp) with h6608 | h6608
                            · rcases p6587_3 (m.d 1 2) (by simp) with h6609 | h6609
                              · linarith only [h0, h6609, hlam]
                              · rcases p6587_3 (m.d 2 3) (by simp) with h6611 | h6611
                                · linarith only [h4, h6611, hlam]
                                · rcases p6587_3 (m.d 2 4) (by simp) with h6613 | h6613
                                  · linarith only [h5, h6613, hlam]
                                  · rcases p6587_3 (m.d 2 5) (by simp) with h6615 | h6615
                                    · linarith only [h6615, hlam, p6587_0]
                                    · rcases h4bigk with h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c | h6617c
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        rcases p6617_3 (m.d 0 4) (by simp) with h6619 | h6619
                                        · rcases p6617_3 (m.d 1 4) (by simp) with h6620 | h6620
                                          · linarith only [h2, h6620, hlam]
                                          · rcases p6617_3 (m.d 2 4) (by simp) with h6622 | h6622
                                            · linarith only [h5, h6622, hlam]
                                            · linarith only [h3576, h6622, hlam]
                                        · linarith only [h2, h6619, hlam]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        rcases p6617_3 (m.d 0 4) (by simp) with h6626 | h6626
                                        · rcases p6617_3 (m.d 1 4) (by simp) with h6627 | h6627
                                          · linarith only [h2, h6627, hlam]
                                          · rcases p6617_3 (m.d 2 4) (by simp) with h6629 | h6629
                                            · linarith only [h5, h6629, hlam]
                                            · rcases p6617_3 (m.d 3 4) (by simp) with h6631 | h6631
                                              · linarith only [h6631, h7, hlam]
                                              · rcases p6617_3 (m.d 4 5) (by simp) with h6633 | h6633
                                                · linarith only [h6633, h9, hlam]
                                                · linarith only [h6442, h6633, hlam]
                                        · linarith only [h5, h6626, hlam]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h10, h4129, h6440, h6444, h9, hlam, p6617_2]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h0, h3576, h4, h6439, h6440, h6444, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6617_1]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h2, hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h3576, hlam, p6617_1]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h3576, h6439, h6440, h6444, hc34, hc45, hlam, hphi, p6617_1]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h6437, hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h5, hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h6439, h6440, h6444, hc14, hc45, hlam, hphi, p6617_1]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h0, h4, h6439, h6440, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6617_1]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h6442, hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h7, hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h4129, hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h6439, hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h6444, hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h9, hlam, p6617_0]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        rcases p6617_3 (m.d 0 4) (by simp) with h6655 | h6655
                                        · rcases p6617_3 (m.d 1 4) (by simp) with h6656 | h6656
                                          · linarith only [h6656, hlam, p6617_0]
                                          · rcases p6617_3 (m.d 2 4) (by simp) with h6658 | h6658
                                            · linarith only [h6442, h6658, hlam]
                                            · linarith only [h3576, h6658, hlam]
                                        · linarith only [h2, h6655, hlam]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [h0, h3576, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6617_1]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        rcases p6617_3 (m.d 0 4) (by simp) with h6663 | h6663
                                        · rcases p6617_3 (m.d 1 4) (by simp) with h6664 | h6664
                                          · linarith only [h6437, h6664, hlam]
                                          · linarith only [h4129, h6664, hlam]
                                        · linarith only [h6663, h7, hlam]
                                      · have p6617_0 := h6617c.1
                                        have p6617_1 := h6617c.2.1
                                        have p6617_2 := h6617c.2.2.1
                                        have p6617_3 := h6617c.2.2.2
                                        linarith only [hlam, p6617_0]
                            · linarith only [h6608, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h0, hlam, p6587_1]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h10, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h3576, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h4058, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h4, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h0, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6587_1]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h0, h3576, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6587_1]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h6440, hlam, p6587_1]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h5, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h0, h4, h6439, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6587_1]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h6439, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h6442, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h6, hlam, p6587_0]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            rcases p6587_3 (m.d 0 2) (by simp) with h6686 | h6686
                            · rcases p6587_3 (m.d 1 2) (by simp) with h6687 | h6687
                              · linarith only [h6687, hlam, p6587_0]
                              · rcases p6587_3 (m.d 2 3) (by simp) with h6689 | h6689
                                · linarith only [h6440, h6689, hlam]
                                · linarith only [h10, h6689, hlam]
                            · linarith only [h0, h6686, hlam]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h0, h10, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6587_1]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [h0, h3576, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6587_1]
                          · have p6587_0 := h6587c.1
                            have p6587_1 := h6587c.2.1
                            have p6587_2 := h6587c.2.2.1
                            have p6587_3 := h6587c.2.2.2
                            linarith only [hlam, p6587_0]
                        · rcases h2bigk with h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c | h6696c
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h3576, h4, h6439, h6440, h6444, h7, h9, hlam, p6696_2]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            rcases p6696_3 (m.d 0 2) (by simp) with h6699 | h6699
                            · rcases p6696_3 (m.d 1 2) (by simp) with h6700 | h6700
                              · linarith only [h0, h6700, hlam]
                              · rcases p6696_3 (m.d 2 3) (by simp) with h6702 | h6702
                                · linarith only [h6702, hlam, p6696_0]
                                · rcases p6696_3 (m.d 2 4) (by simp) with h6704 | h6704
                                  · linarith only [h5, h6704, hlam]
                                  · rcases p6696_3 (m.d 2 5) (by simp) with h6706 | h6706
                                    · linarith only [h6, h6706, hlam]
                                    · linarith only [h6440, h6706, hlam]
                            · linarith only [h6699, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            rcases p6696_3 (m.d 0 2) (by simp) with h6710 | h6710
                            · rcases p6696_3 (m.d 1 2) (by simp) with h6711 | h6711
                              · linarith only [h0, h6711, hlam]
                              · rcases p6696_3 (m.d 2 3) (by simp) with h6713 | h6713
                                · linarith only [h4, h6713, hlam]
                                · linarith only [h6439, h6713, hlam]
                            · linarith only [h6710, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            rcases p6696_3 (m.d 0 2) (by simp) with h6717 | h6717
                            · rcases p6696_3 (m.d 1 2) (by simp) with h6718 | h6718
                              · linarith only [h0, h6718, hlam]
                              · rcases p6696_3 (m.d 2 3) (by simp) with h6720 | h6720
                                · linarith only [h4, h6720, hlam]
                                · rcases p6696_3 (m.d 2 4) (by simp) with h6722 | h6722
                                  · linarith only [h5, h6722, hlam]
                                  · rcases p6696_3 (m.d 2 5) (by simp) with h6724 | h6724
                                    · linarith only [h6724, hlam, p6696_0]
                                    · rcases h4bigk with h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c | h6726c
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        rcases p6726_3 (m.d 0 4) (by simp) with h6728 | h6728
                                        · rcases p6726_3 (m.d 1 4) (by simp) with h6729 | h6729
                                          · linarith only [h2, h6729, hlam]
                                          · rcases p6726_3 (m.d 2 4) (by simp) with h6731 | h6731
                                            · linarith only [h5, h6731, hlam]
                                            · linarith only [h3576, h6731, hlam]
                                        · linarith only [h2, h6728, hlam]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        rcases p6726_3 (m.d 0 4) (by simp) with h6735 | h6735
                                        · rcases p6726_3 (m.d 1 4) (by simp) with h6736 | h6736
                                          · linarith only [h2, h6736, hlam]
                                          · rcases p6726_3 (m.d 2 4) (by simp) with h6738 | h6738
                                            · linarith only [h5, h6738, hlam]
                                            · rcases p6726_3 (m.d 3 4) (by simp) with h6740 | h6740
                                              · linarith only [h6740, h7, hlam]
                                              · rcases p6726_3 (m.d 4 5) (by simp) with h6742 | h6742
                                                · linarith only [h6742, h9, hlam]
                                                · linarith only [h6442, h6742, hlam]
                                        · linarith only [h5, h6735, hlam]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h10, h4129, h6440, h6444, h9, hlam, p6726_2]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h0, h3576, h4, h6439, h6440, h6444, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6726_1]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h2, hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h3576, hlam, p6726_1]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h3576, h6439, h6440, h6444, hc34, hc45, hlam, hphi, p6726_1]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h6437, hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h5, hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h6439, h6440, h6444, hc14, hc45, hlam, hphi, p6726_1]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h0, h4, h6439, h6440, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6726_1]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h6442, hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h7, hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h4129, hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h6439, hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h6444, hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h9, hlam, p6726_0]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        rcases p6726_3 (m.d 0 4) (by simp) with h6764 | h6764
                                        · rcases p6726_3 (m.d 1 4) (by simp) with h6765 | h6765
                                          · linarith only [h6765, hlam, p6726_0]
                                          · rcases p6726_3 (m.d 2 4) (by simp) with h6767 | h6767
                                            · linarith only [h6442, h6767, hlam]
                                            · linarith only [h3576, h6767, hlam]
                                        · linarith only [h2, h6764, hlam]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [h0, h3576, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6726_1]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        rcases p6726_3 (m.d 0 4) (by simp) with h6772 | h6772
                                        · rcases p6726_3 (m.d 1 4) (by simp) with h6773 | h6773
                                          · linarith only [h6437, h6773, hlam]
                                          · linarith only [h4129, h6773, hlam]
                                        · linarith only [h6772, h7, hlam]
                                      · have p6726_0 := h6726c.1
                                        have p6726_1 := h6726c.2.1
                                        have p6726_2 := h6726c.2.2.1
                                        have p6726_3 := h6726c.2.2.2
                                        linarith only [hlam, p6726_0]
                            · linarith only [h6717, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h0, hlam, p6696_1]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h10, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h3576, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h4058, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h4, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h0, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6696_1]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h0, h3576, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6696_1]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h6440, hlam, p6696_1]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h5, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h0, h4, h6439, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6696_1]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h6439, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h6442, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h6, hlam, p6696_0]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            rcases p6696_3 (m.d 0 2) (by simp) with h6795 | h6795
                            · rcases p6696_3 (m.d 1 2) (by simp) with h6796 | h6796
                              · linarith only [h6796, hlam, p6696_0]
                              · rcases p6696_3 (m.d 2 3) (by simp) with h6798 | h6798
                                · linarith only [h6440, h6798, hlam]
                                · linarith only [h10, h6798, hlam]
                            · linarith only [h0, h6795, hlam]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h0, h10, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6696_1]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [h0, h3576, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6696_1]
                          · have p6696_0 := h6696c.1
                            have p6696_1 := h6696c.2.1
                            have p6696_2 := h6696c.2.2.1
                            have p6696_3 := h6696c.2.2.2
                            linarith only [hlam, p6696_0]
                        · rcases h2bigk with h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c | h6805c
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h3576, h4, h6439, h6440, h6444, h7, h9, hlam, p6805_2]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            rcases p6805_3 (m.d 0 2) (by simp) with h6808 | h6808
                            · rcases p6805_3 (m.d 1 2) (by simp) with h6809 | h6809
                              · linarith only [h0, h6809, hlam]
                              · rcases p6805_3 (m.d 2 3) (by simp) with h6811 | h6811
                                · linarith only [h6811, hlam, p6805_0]
                                · rcases p6805_3 (m.d 2 4) (by simp) with h6813 | h6813
                                  · linarith only [h5, h6813, hlam]
                                  · rcases p6805_3 (m.d 2 5) (by simp) with h6815 | h6815
                                    · linarith only [h6, h6815, hlam]
                                    · linarith only [h6440, h6815, hlam]
                            · linarith only [h6808, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            rcases p6805_3 (m.d 0 2) (by simp) with h6819 | h6819
                            · rcases p6805_3 (m.d 1 2) (by simp) with h6820 | h6820
                              · linarith only [h0, h6820, hlam]
                              · rcases p6805_3 (m.d 2 3) (by simp) with h6822 | h6822
                                · linarith only [h4, h6822, hlam]
                                · linarith only [h6439, h6822, hlam]
                            · linarith only [h6819, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            rcases p6805_3 (m.d 0 2) (by simp) with h6826 | h6826
                            · rcases p6805_3 (m.d 1 2) (by simp) with h6827 | h6827
                              · linarith only [h0, h6827, hlam]
                              · rcases p6805_3 (m.d 2 3) (by simp) with h6829 | h6829
                                · linarith only [h4, h6829, hlam]
                                · rcases p6805_3 (m.d 2 4) (by simp) with h6831 | h6831
                                  · linarith only [h5, h6831, hlam]
                                  · rcases p6805_3 (m.d 2 5) (by simp) with h6833 | h6833
                                    · linarith only [h6833, hlam, p6805_0]
                                    · rcases h4bigk with h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c | h6835c
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        rcases p6835_3 (m.d 0 4) (by simp) with h6837 | h6837
                                        · rcases p6835_3 (m.d 1 4) (by simp) with h6838 | h6838
                                          · linarith only [h2, h6838, hlam]
                                          · rcases p6835_3 (m.d 2 4) (by simp) with h6840 | h6840
                                            · linarith only [h5, h6840, hlam]
                                            · linarith only [h3576, h6840, hlam]
                                        · linarith only [h2, h6837, hlam]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        rcases p6835_3 (m.d 0 4) (by simp) with h6844 | h6844
                                        · rcases p6835_3 (m.d 1 4) (by simp) with h6845 | h6845
                                          · linarith only [h2, h6845, hlam]
                                          · rcases p6835_3 (m.d 2 4) (by simp) with h6847 | h6847
                                            · linarith only [h5, h6847, hlam]
                                            · rcases p6835_3 (m.d 3 4) (by simp) with h6849 | h6849
                                              · linarith only [h6849, h7, hlam]
                                              · rcases p6835_3 (m.d 4 5) (by simp) with h6851 | h6851
                                                · linarith only [h6851, h9, hlam]
                                                · linarith only [h6442, h6851, hlam]
                                        · linarith only [h5, h6844, hlam]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h10, h4129, h6440, h6444, h9, hlam, p6835_2]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h0, h3576, h4, h6439, h6440, h6444, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6835_1]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h2, hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h3576, hlam, p6835_1]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h3576, h6439, h6440, h6444, hc34, hc45, hlam, hphi, p6835_1]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h6437, hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h5, hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h6439, h6440, h6444, hc14, hc45, hlam, hphi, p6835_1]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h0, h4, h6439, h6440, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6835_1]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h6442, hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h7, hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h4129, hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h6439, hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h6444, hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h9, hlam, p6835_0]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        rcases p6835_3 (m.d 0 4) (by simp) with h6873 | h6873
                                        · rcases p6835_3 (m.d 1 4) (by simp) with h6874 | h6874
                                          · linarith only [h6874, hlam, p6835_0]
                                          · rcases p6835_3 (m.d 2 4) (by simp) with h6876 | h6876
                                            · linarith only [h6442, h6876, hlam]
                                            · linarith only [h3576, h6876, hlam]
                                        · linarith only [h2, h6873, hlam]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [h0, h3576, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6835_1]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        rcases p6835_3 (m.d 0 4) (by simp) with h6881 | h6881
                                        · rcases p6835_3 (m.d 1 4) (by simp) with h6882 | h6882
                                          · linarith only [h6437, h6882, hlam]
                                          · linarith only [h4129, h6882, hlam]
                                        · linarith only [h6881, h7, hlam]
                                      · have p6835_0 := h6835c.1
                                        have p6835_1 := h6835c.2.1
                                        have p6835_2 := h6835c.2.2.1
                                        have p6835_3 := h6835c.2.2.2
                                        linarith only [hlam, p6835_0]
                            · linarith only [h6826, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h0, hlam, p6805_1]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h10, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h3576, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h4058, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h4, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h0, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6805_1]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h0, h3576, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6805_1]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h6440, hlam, p6805_1]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h5, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h0, h4, h6439, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6805_1]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h6439, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h6442, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h6, hlam, p6805_0]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            rcases p6805_3 (m.d 0 2) (by simp) with h6904 | h6904
                            · rcases p6805_3 (m.d 1 2) (by simp) with h6905 | h6905
                              · linarith only [h6905, hlam, p6805_0]
                              · rcases p6805_3 (m.d 2 3) (by simp) with h6907 | h6907
                                · linarith only [h6440, h6907, hlam]
                                · linarith only [h10, h6907, hlam]
                            · linarith only [h0, h6904, hlam]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h0, h10, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6805_1]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [h0, h3576, h4, h6440, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6805_1]
                          · have p6805_0 := h6805c.1
                            have p6805_1 := h6805c.2.1
                            have p6805_2 := h6805c.2.2.1
                            have p6805_3 := h6805c.2.2.2
                            linarith only [hlam, p6805_0]
              · linarith only [h6467, hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h0, hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h10, hlam, p6446_1]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h3576, hlam, p6446_1]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h4058, hlam, p6446_1]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h1, hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h0, h4, h4130, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6446_1]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h0, h3576, h4, h4130, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6446_1]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h4130, hlam, p6446_1]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h2, hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h0, h4, h4129, h4130, h6444, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6446_1]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h4129, hlam, p6446_1]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h6437, hlam, p6446_1]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h3, hlam, p6446_0]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              rcases p6446_3 (m.d 0 1) (by simp) with h6931 | h6931
              · rcases p6446_3 (m.d 1 2) (by simp) with h6932 | h6932
                · linarith only [h4058, h6932, hlam]
                · rcases p6446_3 (m.d 1 3) (by simp) with h6934 | h6934
                  · linarith only [h4130, h6934, hlam]
                  · linarith only [h10, h6934, hlam]
              · linarith only [h0, h6931, hlam]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [h0, h4, h4058, h4129, h6440, h6444, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6446_1]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              rcases p6446_3 (m.d 0 1) (by simp) with h6939 | h6939
              · rcases p6446_3 (m.d 1 2) (by simp) with h6940 | h6940
                · linarith only [h4058, h6940, hlam]
                · rcases p6446_3 (m.d 1 3) (by simp) with h6942 | h6942
                  · linarith only [h4130, h6942, hlam]
                  · linarith only [h4129, h6942, hlam]
              · linarith only [h2, h6939, hlam]
            · have p6446_0 := h6446c.1
              have p6446_1 := h6446c.2.1
              have p6446_2 := h6446c.2.2.1
              have p6446_3 := h6446c.2.2.2
              linarith only [hlam, p6446_0]
    · linarith only [h1, h10, h4129, h6439, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16 (m : N7Model)
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  rcases m.htr 1 3 5 (by decide) (by decide) with h4130 | h4130
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130

set_option maxHeartbeats 10278000 in
set_option maxHeartbeats 10278000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x0 (m : N7Model)
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h3576 h4058 h4129

end R2N4
