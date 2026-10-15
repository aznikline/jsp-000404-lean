import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S16
import Jsp000404.R1LeavesN7_0S20
import Jsp000404.R1LeavesN7_0S21
import Jsp000404.R1LeavesN7_0S23

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1 (m : N7Model)
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
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10760 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h11236 | h11236
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h10760 h11236
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h10760 h11236

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1 (m : N7Model)
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
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h10760 | h10760
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h10760
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h10760

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17 (m : N7Model)
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
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h9268 | h9268
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268

set_option maxHeartbeats 25422000 in
set_option maxHeartbeats 25422000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s8 (m : N7Model)
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s9 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

set_option maxHeartbeats 26552000 in
set_option maxHeartbeats 26552000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s7 (m : N7Model)
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s8 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8
  · rcases m.htr 0 4 5 (by decide) (by decide) with h12720 | h12720
    · linarith only [h12720, h7, h8, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h12722 | h12722
      · rcases m.htr 1 2 4 (by decide) (by decide) with h12723 | h12723
        · rcases m.htr 1 2 5 (by decide) (by decide) with h12724 | h12724
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12725 | h12725
            · rcases m.htr 1 3 5 (by decide) (by decide) with h12726 | h12726
              · linarith only [h1, h12726, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12728 | h12728
                · linarith only [h12720, h12728, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12730 | h12730
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12731 | h12731
                    · linarith only [h1, h12722, h12731, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12733 | h12733
                      · linarith only [h12720, h12723, h12733, h2, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12735 | h12735
                        · linarith only [h12720, h12724, h12730, h12731, h12735, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h1bigk with h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c | h12737c
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h12722, h12730, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12737_1]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            rcases p12737_3 (m.d 0 1) (by simp) with h12740 | h12740
                            · rcases p12737_3 (m.d 1 2) (by simp) with h12741 | h12741
                              · linarith only [h0, h12741, hlam]
                              · linarith only [h12722, h12741, hlam]
                            · linarith only [h12740, hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            rcases p12737_3 (m.d 0 1) (by simp) with h12745 | h12745
                            · rcases p12737_3 (m.d 1 2) (by simp) with h12746 | h12746
                              · linarith only [h0, h12746, hlam]
                              · linarith only [h12723, h12746, hlam]
                            · linarith only [h12745, hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            rcases p12737_3 (m.d 0 1) (by simp) with h12750 | h12750
                            · rcases p12737_3 (m.d 1 2) (by simp) with h12751 | h12751
                              · linarith only [h0, h12751, hlam]
                              · linarith only [h12724, h12751, hlam]
                            · linarith only [h12750, hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h0, hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h0, h12722, h12730, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12737_1]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            rcases p12737_3 (m.d 0 1) (by simp) with h12758 | h12758
                            · rcases p12737_3 (m.d 1 2) (by simp) with h12759 | h12759
                              · rcases p12737_3 (m.d 1 3) (by simp) with h12760 | h12760
                                · linarith only [h12722, h12760, hlam]
                                · linarith only [h12725, h12760, hlam]
                              · linarith only [h12723, h12759, hlam]
                            · linarith only [h12758, h2, hlam]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h0, h12722, h12726, h12730, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12737_1]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h1, hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h12722, hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h1, h12723, h12730, h12735, h8, hc34, hc45, hlam, hphi, p12737_1]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h12726, hlam, p12737_1]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h2, hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h12723, hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h12725, hlam, p12737_1]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h12728, hlam, p12737_1]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h3, hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h12724, hlam, p12737_0]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [h12722, h12730, h12735, h3, h8, hc34, hc45, hlam, hphi, p12737_1]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            rcases p12737_3 (m.d 0 1) (by simp) with h12779 | h12779
                            · rcases p12737_3 (m.d 1 2) (by simp) with h12780 | h12780
                              · rcases p12737_3 (m.d 1 3) (by simp) with h12781 | h12781
                                · linarith only [h12726, h12781, hlam]
                                · linarith only [h12725, h12781, hlam]
                              · linarith only [h12723, h12780, hlam]
                            · linarith only [h12779, h2, hlam]
                          · have p12737_0 := h12737c.1
                            have p12737_1 := h12737c.2.1
                            have p12737_2 := h12737c.2.2.1
                            have p12737_3 := h12737c.2.2.2
                            linarith only [hlam, p12737_0]
                  · linarith only [h12730, h7, h8, hc23, hc35, hlam, hphi]
            · linarith only [h12722, h12725, h7, h8, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12789 | h12789
            · rcases m.htr 1 3 5 (by decide) (by decide) with h12790 | h12790
              · linarith only [h0, h12722, h12724, h12790, h6, h8, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12792 | h12792
                · linarith only [h12720, h12722, h12724, h12789, h12792, h2, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12794 | h12794
                  · linarith only [h0, h12722, h12724, h12794, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h12794, h7, h8, hc23, hc35, hlam, hphi]
            · linarith only [h12789, h7, h8, hc13, hc35, hlam, hphi]
        · linarith only [h12720, h12722, h12723, h5, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h12799 | h12799
        · rcases m.htr 1 2 5 (by decide) (by decide) with h12800 | h12800
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12801 | h12801
            · rcases m.htr 1 3 5 (by decide) (by decide) with h12802 | h12802
              · linarith only [h12722, h12799, h12802, h4, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h12722, h12800, h12802, hlam]
            · linarith only [h12722, h12799, h12801, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12806 | h12806
            · rcases m.htr 1 3 5 (by decide) (by decide) with h12807 | h12807
              · linarith only [h1, h12807, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12809 | h12809
                · linarith only [h12720, h12722, h12799, h12809, h4, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12811 | h12811
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12812 | h12812
                    · linarith only [h12812, h4, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12814 | h12814
                      · linarith only [h12720, h12799, h12814, h2, h7, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12816 | h12816
                        · linarith only [h0, h12720, h12722, h12799, h12811, h12812, h12816, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h12722, h12799, h12811, h12816, h4, h8, hc34, hc45, hlam, hphi]
                  · linarith only [h12722, h12799, h12811, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h12722, h12799, h12806, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h12821 | h12821
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12822 | h12822
            · rcases m.htr 1 3 5 (by decide) (by decide) with h12823 | h12823
              · linarith only [h1, h12823, h8, hlam]
              · linarith only [h12720, h12799, h12821, h12822, h12823, h5, hc34, hc45, hlam, hphi]
            · linarith only [h12722, h12821, h12822, h7, h8, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12827 | h12827
            · rcases m.htr 1 3 5 (by decide) (by decide) with h12828 | h12828
              · linarith only [h1, h12828, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12830 | h12830
                · linarith only [h12720, h12722, h12799, h12827, h12830, h5, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12832 | h12832
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12833 | h12833
                    · linarith only [h12833, h4, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12835 | h12835
                      · linarith only [h12720, h12835, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12837 | h12837
                        · linarith only [h12720, h12799, h12837, h5, hc12, hc34, hlam, hphi, ht23]
                        · rcases h1bigk with h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c | h12839c
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            rcases p12839_3 (m.d 0 1) (by simp) with h12841 | h12841
                            · rcases p12839_3 (m.d 1 2) (by simp) with h12842 | h12842
                              · linarith only [h12842, hlam, p12839_0]
                              · rcases p12839_3 (m.d 1 3) (by simp) with h12844 | h12844
                                · linarith only [h1, h12844, hlam]
                                · linarith only [h12722, h12844, hlam]
                            · linarith only [h12841, hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            rcases p12839_3 (m.d 0 1) (by simp) with h12848 | h12848
                            · rcases p12839_3 (m.d 1 2) (by simp) with h12849 | h12849
                              · linarith only [h0, h12849, hlam]
                              · rcases p12839_3 (m.d 1 3) (by simp) with h12851 | h12851
                                · linarith only [h12851, hlam, p12839_0]
                                · rcases p12839_3 (m.d 1 4) (by simp) with h12853 | h12853
                                  · linarith only [h12853, h2, hlam]
                                  · rcases p12839_3 (m.d 1 5) (by simp) with h12855 | h12855
                                    · linarith only [h12855, h3, hlam]
                                    · linarith only [h12828, h12855, hlam]
                            · linarith only [h12848, hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            rcases p12839_3 (m.d 0 1) (by simp) with h12859 | h12859
                            · rcases p12839_3 (m.d 1 2) (by simp) with h12860 | h12860
                              · linarith only [h0, h12860, hlam]
                              · rcases p12839_3 (m.d 1 3) (by simp) with h12862 | h12862
                                · linarith only [h1, h12862, hlam]
                                · linarith only [h12827, h12862, hlam]
                            · linarith only [h12859, hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            rcases p12839_3 (m.d 0 1) (by simp) with h12866 | h12866
                            · rcases p12839_3 (m.d 1 2) (by simp) with h12867 | h12867
                              · linarith only [h0, h12867, hlam]
                              · rcases p12839_3 (m.d 1 3) (by simp) with h12869 | h12869
                                · linarith only [h1, h12869, hlam]
                                · rcases p12839_3 (m.d 1 4) (by simp) with h12871 | h12871
                                  · linarith only [h12871, h2, hlam]
                                  · rcases p12839_3 (m.d 1 5) (by simp) with h12873 | h12873
                                    · linarith only [h12873, hlam, p12839_0]
                                    · rcases h1emax with h12875 | h12875 | h12875 | h12875 | h12875
                                      · linarith only [h12828, h12875, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12839_1]
                                      · rcases h2bigk with h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          rcases p12877_3 (m.d 0 2) (by simp) with h12879 | h12879
                                          · rcases p12877_3 (m.d 1 2) (by simp) with h12880 | h12880
                                            · linarith only [h0, h12880, hlam]
                                            · rcases p12877_3 (m.d 2 3) (by simp) with h12882 | h12882
                                              · linarith only [h12882, h4, hlam]
                                              · linarith only [h12722, h12882, hlam]
                                          · linarith only [h0, h12879, hlam]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          rcases p12877_3 (m.d 0 2) (by simp) with h12886 | h12886
                                          · rcases p12877_3 (m.d 1 2) (by simp) with h12887 | h12887
                                            · linarith only [h0, h12887, hlam]
                                            · rcases p12877_3 (m.d 2 3) (by simp) with h12889 | h12889
                                              · linarith only [h12889, hlam, p12877_0]
                                              · rcases p12877_3 (m.d 2 4) (by simp) with h12891 | h12891
                                                · linarith only [h12891, h5, hlam]
                                                · rcases p12877_3 (m.d 2 5) (by simp) with h12893 | h12893
                                                  · linarith only [h12893, h6, hlam]
                                                  · linarith only [h12833, h12893, hlam]
                                          · linarith only [h12886, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          rcases p12877_3 (m.d 0 2) (by simp) with h12897 | h12897
                                          · rcases p12877_3 (m.d 1 2) (by simp) with h12898 | h12898
                                            · linarith only [h0, h12898, hlam]
                                            · rcases p12877_3 (m.d 2 3) (by simp) with h12900 | h12900
                                              · linarith only [h12900, h4, hlam]
                                              · linarith only [h12832, h12900, hlam]
                                          · linarith only [h12897, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          rcases p12877_3 (m.d 0 2) (by simp) with h12904 | h12904
                                          · rcases p12877_3 (m.d 1 2) (by simp) with h12905 | h12905
                                            · linarith only [h0, h12905, hlam]
                                            · rcases p12877_3 (m.d 2 3) (by simp) with h12907 | h12907
                                              · linarith only [h12907, h4, hlam]
                                              · rcases p12877_3 (m.d 2 4) (by simp) with h12909 | h12909
                                                · linarith only [h12909, h5, hlam]
                                                · rcases p12877_3 (m.d 2 5) (by simp) with h12911 | h12911
                                                  · linarith only [h12911, hlam, p12877_0]
                                                  · rcases h4bigk with h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c | h12913c
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12837, h7, h8, hc14, hc45, hlam, hphi, p12913_1]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12799, h12837, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p12913_1]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12837, h7, h8, hc34, hc45, hlam, hphi, p12913_1]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12720, hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h2, hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12799, hlam, p12913_1]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12837, h2, h7, h8, hc34, hc45, hlam, hphi, p12913_1]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12830, hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h5, hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h0, h12832, h12833, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p12877_1, p12913_1]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h0, h12832, h12833, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12877_1, p12913_1]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12835, hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h7, hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12827, hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12832, hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12837, hlam, p12913_0]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12799, h5, hc12, hc45, hlam, hphi, ht23, ht34, p12913_1]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      rcases p12913_3 (m.d 0 4) (by simp) with h12935 | h12935
                                                      · linarith only [h12720, h12935, hlam]
                                                      · linarith only [h12935, h2, hlam]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [h12799, hc12, hc45, hlam, hphi, ht23, ht34, p12913_1]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      rcases p12913_3 (m.d 0 4) (by simp) with h12939 | h12939
                                                      · linarith only [h12720, h12939, hlam]
                                                      · linarith only [h12939, h7, hlam]
                                                    · have p12913_0 := h12913c.1
                                                      have p12913_1 := h12913c.2.1
                                                      have p12913_2 := h12913c.2.2.1
                                                      have p12913_3 := h12913c.2.2.2
                                                      linarith only [hlam, p12913_0]
                                          · linarith only [h12904, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h0, hlam, p12877_1]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h12722, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h12799, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h12821, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h4, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h12837, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p12877_1]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h12799, h12837, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p12877_1]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h12833, hlam, p12877_1]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h5, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h12837, h5, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p12877_1]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h12832, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h12835, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h6, hlam, p12877_0]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          rcases p12877_3 (m.d 0 2) (by simp) with h12960 | h12960
                                          · rcases p12877_3 (m.d 1 2) (by simp) with h12961 | h12961
                                            · linarith only [h12961, hlam, p12877_0]
                                            · rcases p12877_3 (m.d 2 3) (by simp) with h12963 | h12963
                                              · linarith only [h12833, h12963, hlam]
                                              · linarith only [h12722, h12963, hlam]
                                          · linarith only [h0, h12960, hlam]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h12722, hc12, hc25, hlam, hphi, p12877_1]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [h0, h12799, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12877_1]
                                        · have p12877_0 := h12877c.1
                                          have p12877_1 := h12877c.2.1
                                          have p12877_2 := h12877c.2.2.1
                                          have p12877_3 := h12877c.2.2.2
                                          linarith only [hlam, p12877_0]
                                      · rcases h2bigk with h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c | h12970c
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          rcases p12970_3 (m.d 0 2) (by simp) with h12972 | h12972
                                          · rcases p12970_3 (m.d 1 2) (by simp) with h12973 | h12973
                                            · linarith only [h0, h12973, hlam]
                                            · rcases p12970_3 (m.d 2 3) (by simp) with h12975 | h12975
                                              · linarith only [h12975, h4, hlam]
                                              · linarith only [h12722, h12975, hlam]
                                          · linarith only [h0, h12972, hlam]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          rcases p12970_3 (m.d 0 2) (by simp) with h12979 | h12979
                                          · rcases p12970_3 (m.d 1 2) (by simp) with h12980 | h12980
                                            · linarith only [h0, h12980, hlam]
                                            · rcases p12970_3 (m.d 2 3) (by simp) with h12982 | h12982
                                              · linarith only [h12982, hlam, p12970_0]
                                              · rcases p12970_3 (m.d 2 4) (by simp) with h12984 | h12984
                                                · linarith only [h12984, h5, hlam]
                                                · rcases p12970_3 (m.d 2 5) (by simp) with h12986 | h12986
                                                  · linarith only [h12986, h6, hlam]
                                                  · linarith only [h12833, h12986, hlam]
                                          · linarith only [h12979, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          rcases p12970_3 (m.d 0 2) (by simp) with h12990 | h12990
                                          · rcases p12970_3 (m.d 1 2) (by simp) with h12991 | h12991
                                            · linarith only [h0, h12991, hlam]
                                            · rcases p12970_3 (m.d 2 3) (by simp) with h12993 | h12993
                                              · linarith only [h12993, h4, hlam]
                                              · linarith only [h12832, h12993, hlam]
                                          · linarith only [h12990, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          rcases p12970_3 (m.d 0 2) (by simp) with h12997 | h12997
                                          · rcases p12970_3 (m.d 1 2) (by simp) with h12998 | h12998
                                            · linarith only [h0, h12998, hlam]
                                            · rcases p12970_3 (m.d 2 3) (by simp) with h13000 | h13000
                                              · linarith only [h13000, h4, hlam]
                                              · rcases p12970_3 (m.d 2 4) (by simp) with h13002 | h13002
                                                · linarith only [h13002, h5, hlam]
                                                · rcases p12970_3 (m.d 2 5) (by simp) with h13004 | h13004
                                                  · linarith only [h13004, hlam, p12970_0]
                                                  · rcases h4bigk with h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c | h13006c
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12799, h12837, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13006_1]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12799, h12837, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13006_1]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12837, h7, h8, hc34, hc45, hlam, hphi, p13006_1]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12720, hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h2, hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12799, hlam, p13006_1]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12837, h2, h7, h8, hc34, hc45, hlam, hphi, p13006_1]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12830, hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h5, hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12832, h12833, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p12970_1, p13006_1]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h0, h12832, h12833, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12970_1, p13006_1]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12835, hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h7, hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12827, hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12832, hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12837, hlam, p13006_0]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12799, h5, hc12, hc45, hlam, hphi, ht23, ht34, p13006_1]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      rcases p13006_3 (m.d 0 4) (by simp) with h13028 | h13028
                                                      · linarith only [h12720, h13028, hlam]
                                                      · linarith only [h13028, h2, hlam]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [h12799, hc12, hc45, hlam, hphi, ht23, ht34, p13006_1]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      rcases p13006_3 (m.d 0 4) (by simp) with h13032 | h13032
                                                      · linarith only [h12720, h13032, hlam]
                                                      · linarith only [h13032, h7, hlam]
                                                    · have p13006_0 := h13006c.1
                                                      have p13006_1 := h13006c.2.1
                                                      have p13006_2 := h13006c.2.2.1
                                                      have p13006_3 := h13006c.2.2.2
                                                      linarith only [hlam, p13006_0]
                                          · linarith only [h12997, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h0, hlam, p12970_1]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h12722, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h12799, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h12821, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h4, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h12837, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p12970_1]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h12799, h12837, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p12970_1]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h12833, hlam, p12970_1]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h5, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h12837, h5, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p12970_1]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h12832, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h12835, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h6, hlam, p12970_0]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          rcases p12970_3 (m.d 0 2) (by simp) with h13053 | h13053
                                          · rcases p12970_3 (m.d 1 2) (by simp) with h13054 | h13054
                                            · linarith only [h13054, hlam, p12970_0]
                                            · rcases p12970_3 (m.d 2 3) (by simp) with h13056 | h13056
                                              · linarith only [h12833, h13056, hlam]
                                              · linarith only [h12722, h13056, hlam]
                                          · linarith only [h0, h13053, hlam]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h12722, hc12, hc25, hlam, hphi, p12970_1]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [h0, h12799, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12970_1]
                                        · have p12970_0 := h12970c.1
                                          have p12970_1 := h12970c.2.1
                                          have p12970_2 := h12970c.2.2.1
                                          have p12970_3 := h12970c.2.2.2
                                          linarith only [hlam, p12970_0]
                                      · rcases h2bigk with h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c | h13063c
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          rcases p13063_3 (m.d 0 2) (by simp) with h13065 | h13065
                                          · rcases p13063_3 (m.d 1 2) (by simp) with h13066 | h13066
                                            · linarith only [h0, h13066, hlam]
                                            · rcases p13063_3 (m.d 2 3) (by simp) with h13068 | h13068
                                              · linarith only [h13068, h4, hlam]
                                              · linarith only [h12722, h13068, hlam]
                                          · linarith only [h0, h13065, hlam]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          rcases p13063_3 (m.d 0 2) (by simp) with h13072 | h13072
                                          · rcases p13063_3 (m.d 1 2) (by simp) with h13073 | h13073
                                            · linarith only [h0, h13073, hlam]
                                            · rcases p13063_3 (m.d 2 3) (by simp) with h13075 | h13075
                                              · linarith only [h13075, hlam, p13063_0]
                                              · rcases p13063_3 (m.d 2 4) (by simp) with h13077 | h13077
                                                · linarith only [h13077, h5, hlam]
                                                · rcases p13063_3 (m.d 2 5) (by simp) with h13079 | h13079
                                                  · linarith only [h13079, h6, hlam]
                                                  · linarith only [h12833, h13079, hlam]
                                          · linarith only [h13072, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          rcases p13063_3 (m.d 0 2) (by simp) with h13083 | h13083
                                          · rcases p13063_3 (m.d 1 2) (by simp) with h13084 | h13084
                                            · linarith only [h0, h13084, hlam]
                                            · rcases p13063_3 (m.d 2 3) (by simp) with h13086 | h13086
                                              · linarith only [h13086, h4, hlam]
                                              · linarith only [h12832, h13086, hlam]
                                          · linarith only [h13083, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          rcases p13063_3 (m.d 0 2) (by simp) with h13090 | h13090
                                          · rcases p13063_3 (m.d 1 2) (by simp) with h13091 | h13091
                                            · linarith only [h0, h13091, hlam]
                                            · rcases p13063_3 (m.d 2 3) (by simp) with h13093 | h13093
                                              · linarith only [h13093, h4, hlam]
                                              · rcases p13063_3 (m.d 2 4) (by simp) with h13095 | h13095
                                                · linarith only [h13095, h5, hlam]
                                                · rcases p13063_3 (m.d 2 5) (by simp) with h13097 | h13097
                                                  · linarith only [h13097, hlam, p13063_0]
                                                  · rcases h4bigk with h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12799, h12837, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13099_1]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12799, h12837, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13099_1]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12837, h7, h8, hc34, hc45, hlam, hphi, p13099_1]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12720, hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h2, hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12799, hlam, p13099_1]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12837, h2, h7, h8, hc34, hc45, hlam, hphi, p13099_1]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12830, hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h5, hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12832, h12833, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p13063_1, p13099_1]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h0, h12832, h12833, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13063_1, p13099_1]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12835, hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h7, hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12827, hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12832, hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12837, hlam, p13099_0]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12799, h5, hc12, hc45, hlam, hphi, ht23, ht34, p13099_1]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      rcases p13099_3 (m.d 0 4) (by simp) with h13121 | h13121
                                                      · linarith only [h12720, h13121, hlam]
                                                      · linarith only [h13121, h2, hlam]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [h12799, hc12, hc45, hlam, hphi, ht23, ht34, p13099_1]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      rcases p13099_3 (m.d 0 4) (by simp) with h13125 | h13125
                                                      · linarith only [h12720, h13125, hlam]
                                                      · linarith only [h13125, h7, hlam]
                                                    · have p13099_0 := h13099c.1
                                                      have p13099_1 := h13099c.2.1
                                                      have p13099_2 := h13099c.2.2.1
                                                      have p13099_3 := h13099c.2.2.2
                                                      linarith only [hlam, p13099_0]
                                          · linarith only [h13090, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h0, hlam, p13063_1]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h12722, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h12799, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h12821, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h4, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h12837, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13063_1]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h12799, h12837, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13063_1]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h12833, hlam, p13063_1]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h5, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h12837, h5, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13063_1]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h12832, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h12835, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h6, hlam, p13063_0]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          rcases p13063_3 (m.d 0 2) (by simp) with h13146 | h13146
                                          · rcases p13063_3 (m.d 1 2) (by simp) with h13147 | h13147
                                            · linarith only [h13147, hlam, p13063_0]
                                            · rcases p13063_3 (m.d 2 3) (by simp) with h13149 | h13149
                                              · linarith only [h12833, h13149, hlam]
                                              · linarith only [h12722, h13149, hlam]
                                          · linarith only [h0, h13146, hlam]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h12722, hc12, hc25, hlam, hphi, p13063_1]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [h0, h12799, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13063_1]
                                        · have p13063_0 := h13063c.1
                                          have p13063_1 := h13063c.2.1
                                          have p13063_2 := h13063c.2.2.1
                                          have p13063_3 := h13063c.2.2.2
                                          linarith only [hlam, p13063_0]
                                      · rcases h2bigk with h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c | h13156c
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          rcases p13156_3 (m.d 0 2) (by simp) with h13158 | h13158
                                          · rcases p13156_3 (m.d 1 2) (by simp) with h13159 | h13159
                                            · linarith only [h0, h13159, hlam]
                                            · rcases p13156_3 (m.d 2 3) (by simp) with h13161 | h13161
                                              · linarith only [h13161, h4, hlam]
                                              · linarith only [h12722, h13161, hlam]
                                          · linarith only [h0, h13158, hlam]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          rcases p13156_3 (m.d 0 2) (by simp) with h13165 | h13165
                                          · rcases p13156_3 (m.d 1 2) (by simp) with h13166 | h13166
                                            · linarith only [h0, h13166, hlam]
                                            · rcases p13156_3 (m.d 2 3) (by simp) with h13168 | h13168
                                              · linarith only [h13168, hlam, p13156_0]
                                              · rcases p13156_3 (m.d 2 4) (by simp) with h13170 | h13170
                                                · linarith only [h13170, h5, hlam]
                                                · rcases p13156_3 (m.d 2 5) (by simp) with h13172 | h13172
                                                  · linarith only [h13172, h6, hlam]
                                                  · linarith only [h12833, h13172, hlam]
                                          · linarith only [h13165, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          rcases p13156_3 (m.d 0 2) (by simp) with h13176 | h13176
                                          · rcases p13156_3 (m.d 1 2) (by simp) with h13177 | h13177
                                            · linarith only [h0, h13177, hlam]
                                            · rcases p13156_3 (m.d 2 3) (by simp) with h13179 | h13179
                                              · linarith only [h13179, h4, hlam]
                                              · linarith only [h12832, h13179, hlam]
                                          · linarith only [h13176, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          rcases p13156_3 (m.d 0 2) (by simp) with h13183 | h13183
                                          · rcases p13156_3 (m.d 1 2) (by simp) with h13184 | h13184
                                            · linarith only [h0, h13184, hlam]
                                            · rcases p13156_3 (m.d 2 3) (by simp) with h13186 | h13186
                                              · linarith only [h13186, h4, hlam]
                                              · rcases p13156_3 (m.d 2 4) (by simp) with h13188 | h13188
                                                · linarith only [h13188, h5, hlam]
                                                · rcases p13156_3 (m.d 2 5) (by simp) with h13190 | h13190
                                                  · linarith only [h13190, hlam, p13156_0]
                                                  · rcases h4bigk with h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c | h13192c
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12799, h12837, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13192_1]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12799, h12837, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13192_1]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12837, h7, h8, hc34, hc45, hlam, hphi, p13192_1]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12720, hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h2, hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12799, hlam, p13192_1]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12837, h2, h7, h8, hc34, hc45, hlam, hphi, p13192_1]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12830, hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h5, hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12832, h12833, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p13156_1, p13192_1]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h0, h12832, h12833, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13156_1, p13192_1]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12835, hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h7, hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12827, hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12832, hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12837, hlam, p13192_0]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12799, h5, hc12, hc45, hlam, hphi, ht23, ht34, p13192_1]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      rcases p13192_3 (m.d 0 4) (by simp) with h13214 | h13214
                                                      · linarith only [h12720, h13214, hlam]
                                                      · linarith only [h13214, h2, hlam]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [h12799, hc12, hc45, hlam, hphi, ht23, ht34, p13192_1]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      rcases p13192_3 (m.d 0 4) (by simp) with h13218 | h13218
                                                      · linarith only [h12720, h13218, hlam]
                                                      · linarith only [h13218, h7, hlam]
                                                    · have p13192_0 := h13192c.1
                                                      have p13192_1 := h13192c.2.1
                                                      have p13192_2 := h13192c.2.2.1
                                                      have p13192_3 := h13192c.2.2.2
                                                      linarith only [hlam, p13192_0]
                                          · linarith only [h13183, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h0, hlam, p13156_1]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h12722, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h12799, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h12821, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h4, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h12837, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13156_1]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h12799, h12837, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13156_1]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h12833, hlam, p13156_1]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h5, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h12837, h5, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p13156_1]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h12832, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h12835, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h6, hlam, p13156_0]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          rcases p13156_3 (m.d 0 2) (by simp) with h13239 | h13239
                                          · rcases p13156_3 (m.d 1 2) (by simp) with h13240 | h13240
                                            · linarith only [h13240, hlam, p13156_0]
                                            · rcases p13156_3 (m.d 2 3) (by simp) with h13242 | h13242
                                              · linarith only [h12833, h13242, hlam]
                                              · linarith only [h12722, h13242, hlam]
                                          · linarith only [h0, h13239, hlam]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h12722, hc12, hc25, hlam, hphi, p13156_1]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [h0, h12799, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13156_1]
                                        · have p13156_0 := h13156c.1
                                          have p13156_1 := h13156c.2.1
                                          have p13156_2 := h13156c.2.2.1
                                          have p13156_3 := h13156c.2.2.2
                                          linarith only [hlam, p13156_0]
                            · linarith only [h12866, hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h0, hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h12722, hlam, p12839_1]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h12799, hlam, p12839_1]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h12821, hlam, p12839_1]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h1, hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h1, h12837, h8, hc12, hc45, hlam, hphi, ht23, ht34, p12839_1]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h12722, h12799, h12837, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p12839_1]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h12828, hlam, p12839_1]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h2, hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h12837, h2, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p12839_1]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h12827, hlam, p12839_1]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h12830, hlam, p12839_1]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h3, hlam, p12839_0]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            rcases p12839_3 (m.d 0 1) (by simp) with h13266 | h13266
                            · rcases p12839_3 (m.d 1 2) (by simp) with h13267 | h13267
                              · linarith only [h12821, h13267, hlam]
                              · rcases p12839_3 (m.d 1 3) (by simp) with h13269 | h13269
                                · linarith only [h12828, h13269, hlam]
                                · linarith only [h12722, h13269, hlam]
                            · linarith only [h0, h13266, hlam]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [h0, h12821, h12827, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12839_1]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            rcases p12839_3 (m.d 0 1) (by simp) with h13274 | h13274
                            · rcases p12839_3 (m.d 1 2) (by simp) with h13275 | h13275
                              · linarith only [h12821, h13275, hlam]
                              · rcases p12839_3 (m.d 1 3) (by simp) with h13277 | h13277
                                · linarith only [h12828, h13277, hlam]
                                · linarith only [h12827, h13277, hlam]
                            · linarith only [h13274, h2, hlam]
                          · have p12839_0 := h12839c.1
                            have p12839_1 := h12839c.2.1
                            have p12839_2 := h12839c.2.2.1
                            have p12839_3 := h12839c.2.2.2
                            linarith only [hlam, p12839_0]
                  · linarith only [h1, h12827, h12832, h8, hc23, hc35, hlam, hphi]
            · linarith only [h12827, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x0 (m : N7Model)
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
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14161 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14162 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14163 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h14159 := hg14159
  linarith only [h1, h14163, h7, hlam]

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x1_x0 (m : N7Model)
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
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14161 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14162 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14163 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h14165 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h14159 := hg14159
  linarith only [h1, h13284, h14165, hlam]

end R2N4
