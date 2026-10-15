import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S74
import Jsp000404.R1LeavesN7_0S75

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h43122 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h43123 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h43124 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h43125 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  linarith only [h33187, h41030, h43125, hlam]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h43122 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h43123 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h43124 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 3 4 (by decide) (by decide) with h43125 | h43125
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h43122 h43123 h43124 h43125
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h43122 h43123 h43124 h43125

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h43122 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h43123 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h43124 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  linarith only [h0, h41029, h43124, hlam]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h43122 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h43123 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 2 5 (by decide) (by decide) with h43124 | h43124
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h43122 h43123 h43124
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h43122 h43123 h43124

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h43122 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h43123 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  linarith only [h0, h41028, h43123, hlam]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h43122 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 2 4 (by decide) (by decide) with h43123 | h43123
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h43122 h43123
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h43122 h43123

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h43122 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  linarith only [h0, h41027, h43122, hlam]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 2 3 (by decide) (by decide) with h43122 | h43122
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h43122
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h43122

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 0 4 5 (by decide) (by decide) with h41032 | h41032
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032

set_option maxHeartbeats 6470000 in
set_option maxHeartbeats 6470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s43 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  rcases m.htr 0 3 5 (by decide) (by decide) with h41031 | h41031
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44 m hb1 hb2 hb4 hb5 h0 h33187 h36828 h39227 h41027 h41028 h41029 h41030 h41031
  · rcases m.htr 0 4 5 (by decide) (by decide) with h43973 | h43973
    · linarith only [h41030, h41031, h43973, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h43975 | h43975
      · rcases m.htr 1 2 4 (by decide) (by decide) with h43976 | h43976
        · rcases m.htr 1 2 5 (by decide) (by decide) with h43977 | h43977
          · rcases m.htr 1 3 4 (by decide) (by decide) with h43978 | h43978
            · rcases m.htr 1 3 5 (by decide) (by decide) with h43979 | h43979
              · rcases m.htr 1 4 5 (by decide) (by decide) with h43980 | h43980
                · rcases m.htr 2 3 4 (by decide) (by decide) with h43981 | h43981
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h43982 | h43982
                    · linarith only [h41027, h41031, h43982, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h43984 | h43984
                      · linarith only [h41028, h43973, h43984, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h43986 | h43986
                        · linarith only [h41027, h41031, h43973, h43975, h43979, h43981, h43986, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h1bigk with h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c | h43988c
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h0, hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h33187, hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h36828, hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h39227, hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            rcases p43988_3 (m.d 0 1) (by simp) with h43994 | h43994
                            · linarith only [h43994, hlam, p43988_0]
                            · rcases p43988_3 (m.d 1 2) (by simp) with h43996 | h43996
                              · rcases p43988_3 (m.d 1 3) (by simp) with h43997 | h43997
                                · linarith only [h43975, h43997, hlam]
                                · linarith only [h33187, h43997, hlam]
                              · linarith only [h43996, hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h41031, h43978, h43980, h43986, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43988_1]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h41027, h41031, h43980, h43981, h43986, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43988_1]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h39227, hc01, hc12, hlam, hphi, p43988_1]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            rcases p43988_3 (m.d 0 1) (by simp) with h44005 | h44005
                            · linarith only [h44005, hlam, p43988_0]
                            · rcases p43988_3 (m.d 1 2) (by simp) with h44007 | h44007
                              · rcases p43988_3 (m.d 1 3) (by simp) with h44008 | h44008
                                · rcases p43988_3 (m.d 1 4) (by simp) with h44009 | h44009
                                  · linarith only [h43978, h44009, hlam]
                                  · linarith only [h36828, h44009, hlam]
                                · linarith only [h44008, hlam, p43988_0]
                              · linarith only [h0, h44007, hlam]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h43975, hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h41027, h41031, h43980, h43981, h43986, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43988_1]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h41027, h41031, h43975, h43980, h43981, h43986, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43988_1]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            rcases p43988_3 (m.d 0 1) (by simp) with h44018 | h44018
                            · linarith only [h44018, hlam, p43988_0]
                            · rcases p43988_3 (m.d 1 2) (by simp) with h44020 | h44020
                              · rcases p43988_3 (m.d 1 3) (by simp) with h44021 | h44021
                                · rcases p43988_3 (m.d 1 4) (by simp) with h44022 | h44022
                                  · rcases p43988_3 (m.d 1 5) (by simp) with h44023 | h44023
                                    · linarith only [h43980, h44023, hlam]
                                    · linarith only [h39227, h44023, hlam]
                                  · linarith only [h44022, hlam, p43988_0]
                                · linarith only [h33187, h44021, hlam]
                              · linarith only [h0, h44020, hlam]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h43976, hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h43978, hlam, p43988_1]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h41027, h41031, h43980, h43981, h43986, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p43988_1]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            rcases p43988_3 (m.d 0 1) (by simp) with h44033 | h44033
                            · linarith only [h44033, hlam, p43988_0]
                            · rcases p43988_3 (m.d 1 2) (by simp) with h44035 | h44035
                              · rcases p43988_3 (m.d 1 3) (by simp) with h44036 | h44036
                                · rcases p43988_3 (m.d 1 4) (by simp) with h44037 | h44037
                                  · rcases p43988_3 (m.d 1 5) (by simp) with h44038 | h44038
                                    · rcases h1emax with h44039 | h44039 | h44039 | h44039 | h44039
                                      · rcases h2bigk with h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c | h44040c
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h0, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          rcases p44040_3 (m.d 0 2) (by simp) with h44043 | h44043
                                          · rcases p44040_3 (m.d 1 2) (by simp) with h44044 | h44044
                                            · rcases p44040_3 (m.d 2 3) (by simp) with h44045 | h44045
                                              · linarith only [h44045, hlam, p44040_0]
                                              · rcases p44040_3 (m.d 2 4) (by simp) with h44047 | h44047
                                                · linarith only [h41028, h44047, hlam]
                                                · rcases p44040_3 (m.d 2 5) (by simp) with h44049 | h44049
                                                  · linarith only [h41029, h44049, hlam]
                                                  · linarith only [h43982, h44049, hlam]
                                            · linarith only [h43975, h44044, hlam]
                                          · linarith only [h44043, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          rcases p44040_3 (m.d 0 2) (by simp) with h44054 | h44054
                                          · rcases p44040_3 (m.d 1 2) (by simp) with h44055 | h44055
                                            · rcases p44040_3 (m.d 2 3) (by simp) with h44056 | h44056
                                              · linarith only [h41027, h44056, hlam]
                                              · linarith only [h43981, h44056, hlam]
                                            · linarith only [h43976, h44055, hlam]
                                          · linarith only [h44054, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          rcases p44040_3 (m.d 0 2) (by simp) with h44061 | h44061
                                          · rcases p44040_3 (m.d 1 2) (by simp) with h44062 | h44062
                                            · rcases p44040_3 (m.d 2 3) (by simp) with h44063 | h44063
                                              · linarith only [h41027, h44063, hlam]
                                              · rcases p44040_3 (m.d 2 4) (by simp) with h44065 | h44065
                                                · linarith only [h41028, h44065, hlam]
                                                · rcases p44040_3 (m.d 2 5) (by simp) with h44067 | h44067
                                                  · linarith only [h44067, hlam, p44040_0]
                                                  · rcases h4bigk with h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c | h44069c
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h36828, hlam, p44069_1]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h41030, h41031, h43981, h43986, hc34, hc45, hlam, hphi, p44069_1]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h41030, h41031, h43986, hc34, hc45, hlam, hphi, p44069_1]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h43973, hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      rcases p44069_3 (m.d 0 4) (by simp) with h44075 | h44075
                                                      · linarith only [h36828, h44075, hlam]
                                                      · rcases p44069_3 (m.d 1 4) (by simp) with h44077 | h44077
                                                        · rcases p44069_3 (m.d 2 4) (by simp) with h44078 | h44078
                                                          · linarith only [h43976, h44078, hlam]
                                                          · rcases p44069_3 (m.d 3 4) (by simp) with h44080 | h44080
                                                            · linarith only [h43978, h44080, hlam]
                                                            · rcases p44069_3 (m.d 4 5) (by simp) with h44082 | h44082
                                                              · linarith only [h43980, h44082, hlam]
                                                              · linarith only [h43973, h44082, hlam]
                                                        · linarith only [h36828, h44077, hlam]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      rcases p44069_3 (m.d 0 4) (by simp) with h44087 | h44087
                                                      · linarith only [h36828, h44087, hlam]
                                                      · linarith only [h41028, h44087, hlam]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h41027, h41031, h43980, h43981, h43986, hlam, p44069_2]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h33187, h41031, h43975, h43978, h43986, hc01, hc12, hlam, hphi, p44069_1]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h41028, hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h43976, hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h41028, h41030, h41031, h43986, hc34, hc45, hlam, hphi, p44069_1]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h43984, hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h41030, hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h43978, hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h43981, hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h43986, hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h36828, h43975, h43978, h43980, hc01, hc12, hlam, hphi, p44069_1]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [h43980, hlam, p44069_0]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      rcases p44069_3 (m.d 0 4) (by simp) with h44104 | h44104
                                                      · linarith only [h43973, h44104, hlam]
                                                      · linarith only [h41028, h44104, hlam]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      rcases p44069_3 (m.d 0 4) (by simp) with h44107 | h44107
                                                      · linarith only [h43973, h44107, hlam]
                                                      · linarith only [h41030, h44107, hlam]
                                                    · have p44069_0 := h44069c.1
                                                      have p44069_1 := h44069c.2.1
                                                      have p44069_2 := h44069c.2.2.1
                                                      have p44069_3 := h44069c.2.2.2
                                                      linarith only [hlam, p44069_0]
                                            · linarith only [h43977, h44062, hlam]
                                          · linarith only [h44061, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h41027, h43981, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p44040_1]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          rcases p44040_3 (m.d 0 2) (by simp) with h44115 | h44115
                                          · linarith only [h0, h44115, hlam]
                                          · linarith only [h41027, h44115, hlam]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          rcases p44040_3 (m.d 0 2) (by simp) with h44118 | h44118
                                          · linarith only [h0, h44118, hlam]
                                          · linarith only [h41028, h44118, hlam]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          rcases p44040_3 (m.d 0 2) (by simp) with h44121 | h44121
                                          · linarith only [h0, h44121, hlam]
                                          · linarith only [h41029, h44121, hlam]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h41027, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h43975, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h41027, h41031, h43975, h43978, h43980, h43986, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p44040_1]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h43982, hlam, p44040_1]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h41028, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h43976, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h43981, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h43984, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h41029, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h43977, hlam, p44040_0]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [h41029, h41031, h43975, h43978, h43980, h43981, h43986, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p44040_1]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          rcases p44040_3 (m.d 0 2) (by simp) with h44137 | h44137
                                          · rcases p44040_3 (m.d 1 2) (by simp) with h44138 | h44138
                                            · rcases p44040_3 (m.d 2 3) (by simp) with h44139 | h44139
                                              · linarith only [h43982, h44139, hlam]
                                              · linarith only [h43981, h44139, hlam]
                                            · linarith only [h43976, h44138, hlam]
                                          · linarith only [h41028, h44137, hlam]
                                        · have p44040_0 := h44040c.1
                                          have p44040_1 := h44040c.2.1
                                          have p44040_2 := h44040c.2.2.1
                                          have p44040_3 := h44040c.2.2.2
                                          linarith only [hlam, p44040_0]
                                      · linarith only [h41031, h43975, h43978, h43980, h43986, h44039, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                      · linarith only [h41027, h41031, h43978, h43980, h43981, h43986, h44039, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                      · linarith only [h41027, h41031, h43980, h43981, h43986, h44039, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                      · linarith only [h44039, hc01, hlam, p43988_1]
                                    · linarith only [h44038, hlam, p43988_0]
                                  · linarith only [h36828, h44037, hlam]
                                · linarith only [h33187, h44036, hlam]
                              · linarith only [h0, h44035, hlam]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h43977, hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h43979, hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [h43980, hlam, p43988_0]
                          · have p43988_0 := h43988c.1
                            have p43988_1 := h43988c.2.1
                            have p43988_2 := h43988c.2.2.1
                            have p43988_3 := h43988c.2.2.2
                            linarith only [hlam, p43988_0]
                  · linarith only [h41030, h41031, h43981, hc23, hc35, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h44158 | h44158
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h44159 | h44159
                    · linarith only [h0, h33187, h41027, h41031, h44159, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h44161 | h44161
                      · linarith only [h36828, h43980, h44161, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h44163 | h44163
                        · linarith only [h41027, h41031, h43979, h43980, h44158, h44163, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h1bigk with h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c | h44165c
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h0, hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h33187, hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h36828, hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h39227, hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            rcases p44165_3 (m.d 0 1) (by simp) with h44171 | h44171
                            · linarith only [h44171, hlam, p44165_0]
                            · rcases p44165_3 (m.d 1 2) (by simp) with h44173 | h44173
                              · rcases p44165_3 (m.d 1 3) (by simp) with h44174 | h44174
                                · linarith only [h43975, h44174, hlam]
                                · linarith only [h33187, h44174, hlam]
                              · linarith only [h44173, hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h41031, h43979, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44165_1]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h36828, hc01, hc12, hlam, hphi, p44165_1]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h39227, hc01, hc12, hlam, hphi, p44165_1]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            rcases p44165_3 (m.d 0 1) (by simp) with h44182 | h44182
                            · linarith only [h44182, hlam, p44165_0]
                            · rcases p44165_3 (m.d 1 2) (by simp) with h44184 | h44184
                              · rcases p44165_3 (m.d 1 3) (by simp) with h44185 | h44185
                                · rcases p44165_3 (m.d 1 4) (by simp) with h44186 | h44186
                                  · linarith only [h43978, h44186, hlam]
                                  · linarith only [h36828, h44186, hlam]
                                · linarith only [h44185, hlam, p44165_0]
                              · linarith only [h0, h44184, hlam]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h43975, hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h36828, hc01, hc13, hlam, hphi, p44165_1]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h39227, h43975, hc01, hc12, hlam, hphi, p44165_1]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h43980, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p44165_1]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h43976, hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h43978, hlam, p44165_1]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h43980, hlam, p44165_1]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            rcases p44165_3 (m.d 0 1) (by simp) with h44200 | h44200
                            · linarith only [h44200, hlam, p44165_0]
                            · rcases p44165_3 (m.d 1 2) (by simp) with h44202 | h44202
                              · rcases p44165_3 (m.d 1 3) (by simp) with h44203 | h44203
                                · rcases p44165_3 (m.d 1 4) (by simp) with h44204 | h44204
                                  · linarith only [h43980, h44204, hlam]
                                  · linarith only [h36828, h44204, hlam]
                                · linarith only [h33187, h44203, hlam]
                              · linarith only [h0, h44202, hlam]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h43977, hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h43979, hlam, p44165_0]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [h36828, hc01, hc15, hlam, hphi, p44165_1]
                          · have p44165_0 := h44165c.1
                            have p44165_1 := h44165c.2.1
                            have p44165_2 := h44165c.2.2.1
                            have p44165_3 := h44165c.2.2.2
                            linarith only [hlam, p44165_0]
                  · linarith only [h41030, h41031, h43975, h43979, h44158, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h44214 | h44214
                · linarith only [h36828, h43973, h43978, h43979, h44214, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h44216 | h44216
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h44217 | h44217
                    · linarith only [h33187, h43979, h44217, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h44219 | h44219
                      · linarith only [h36828, h44214, h44219, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h44221 | h44221
                        · linarith only [h36828, h44214, h44221, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h1bigk with h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c | h44223c
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h0, hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h33187, hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h36828, hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h39227, hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            rcases p44223_3 (m.d 0 1) (by simp) with h44229 | h44229
                            · linarith only [h44229, hlam, p44223_0]
                            · rcases p44223_3 (m.d 1 2) (by simp) with h44231 | h44231
                              · rcases p44223_3 (m.d 1 3) (by simp) with h44232 | h44232
                                · linarith only [h43975, h44232, hlam]
                                · linarith only [h33187, h44232, hlam]
                              · linarith only [h44231, hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h36828, h43978, hc01, hc12, hlam, hphi, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h36828, hc01, hc12, hlam, hphi, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h39227, hc01, hc12, hlam, hphi, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h43979, hc01, hc35, hlam, hphi, ht12, ht23, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h43975, hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h36828, h43979, h44221, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h43979, hlam, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h43978, h43979, h44221, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h43976, hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h43978, hlam, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h44214, hlam, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            rcases p44223_3 (m.d 0 1) (by simp) with h44250 | h44250
                            · linarith only [h44250, hlam, p44223_0]
                            · rcases p44223_3 (m.d 1 2) (by simp) with h44252 | h44252
                              · rcases p44223_3 (m.d 1 3) (by simp) with h44253 | h44253
                                · linarith only [h43979, h44253, hlam]
                                · linarith only [h33187, h44253, hlam]
                              · linarith only [h0, h44252, hlam]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h43977, hlam, p44223_0]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h33187, hc01, hc15, hlam, hphi, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [h36828, hc01, hc15, hlam, hphi, p44223_1]
                          · have p44223_0 := h44223c.1
                            have p44223_1 := h44223c.2.1
                            have p44223_2 := h44223c.2.2.1
                            have p44223_3 := h44223c.2.2.2
                            linarith only [hlam, p44223_0]
                  · linarith only [h41030, h41031, h44216, hc23, hc35, hlam, hphi]
            · linarith only [h33187, h41030, h43978, hlam]
          · linarith only [h0, h41029, h43977, hlam]
        · linarith only [h0, h41028, h43976, hlam]
      · linarith only [h0, h41027, h43975, hlam]

set_option maxHeartbeats 8488000 in
set_option maxHeartbeats 8488000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s42_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s43 m hb1 hb2 hb4 hb5 h0 h33187 h36828 h39227 h41027 h41028 h41029 h41030

set_option maxHeartbeats 8488000 in
set_option maxHeartbeats 8488000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s42_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h41030 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h44266 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  rcases m.htr 0 4 5 (by decide) (by decide) with h44267 | h44267
  · rcases m.htr 1 2 3 (by decide) (by decide) with h44268 | h44268
    · rcases m.htr 1 2 4 (by decide) (by decide) with h44269 | h44269
      · rcases m.htr 1 2 5 (by decide) (by decide) with h44270 | h44270
        · rcases m.htr 1 3 4 (by decide) (by decide) with h44271 | h44271
          · rcases m.htr 1 3 5 (by decide) (by decide) with h44272 | h44272
            · rcases m.htr 1 4 5 (by decide) (by decide) with h44273 | h44273
              · rcases m.htr 2 3 4 (by decide) (by decide) with h44274 | h44274
                · linarith only [h41027, h41030, h44274, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h44276 | h44276
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h44277 | h44277
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h44278 | h44278
                      · rcases h1bigk with h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c | h44279c
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h0, hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h33187, hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h36828, hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h39227, hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          rcases p44279_3 (m.d 0 1) (by simp) with h44285 | h44285
                          · linarith only [h44285, hlam, p44279_0]
                          · rcases p44279_3 (m.d 1 2) (by simp) with h44287 | h44287
                            · rcases p44279_3 (m.d 1 3) (by simp) with h44288 | h44288
                              · linarith only [h44268, h44288, hlam]
                              · linarith only [h33187, h44288, hlam]
                            · linarith only [h44287, hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h41027, h41030, h44271, h44276, h44278, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44279_1]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h36828, hc01, hc12, hlam, hphi, p44279_1]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h39227, hc01, hc12, hlam, hphi, p44279_1]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          rcases p44279_3 (m.d 0 1) (by simp) with h44296 | h44296
                          · linarith only [h44296, hlam, p44279_0]
                          · rcases p44279_3 (m.d 1 2) (by simp) with h44298 | h44298
                            · rcases p44279_3 (m.d 1 3) (by simp) with h44299 | h44299
                              · rcases p44279_3 (m.d 1 4) (by simp) with h44300 | h44300
                                · linarith only [h44271, h44300, hlam]
                                · linarith only [h36828, h44300, hlam]
                              · linarith only [h44299, hlam, p44279_0]
                            · linarith only [h0, h44298, hlam]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h44268, hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h41027, h41030, h44271, h44276, h44278, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p44279_1]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h39227, h44268, hc01, hc12, hlam, hphi, p44279_1]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          rcases p44279_3 (m.d 0 1) (by simp) with h44309 | h44309
                          · linarith only [h44309, hlam, p44279_0]
                          · rcases p44279_3 (m.d 1 2) (by simp) with h44311 | h44311
                            · rcases p44279_3 (m.d 1 3) (by simp) with h44312 | h44312
                              · rcases p44279_3 (m.d 1 4) (by simp) with h44313 | h44313
                                · rcases p44279_3 (m.d 1 5) (by simp) with h44314 | h44314
                                  · linarith only [h44273, h44314, hlam]
                                  · linarith only [h39227, h44314, hlam]
                                · linarith only [h44313, hlam, p44279_0]
                              · linarith only [h33187, h44312, hlam]
                            · linarith only [h0, h44311, hlam]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h44269, hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h44271, hlam, p44279_1]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h39227, hc01, hc14, hlam, hphi, p44279_1]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          rcases p44279_3 (m.d 0 1) (by simp) with h44324 | h44324
                          · linarith only [h44324, hlam, p44279_0]
                          · rcases p44279_3 (m.d 1 2) (by simp) with h44326 | h44326
                            · rcases p44279_3 (m.d 1 3) (by simp) with h44327 | h44327
                              · rcases p44279_3 (m.d 1 4) (by simp) with h44328 | h44328
                                · rcases p44279_3 (m.d 1 5) (by simp) with h44329 | h44329
                                  · rcases h1emax with h44330 | h44330 | h44330 | h44330 | h44330
                                    · rcases h2bigk with h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c | h44331c
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h0, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        rcases p44331_3 (m.d 0 2) (by simp) with h44334 | h44334
                                        · rcases p44331_3 (m.d 1 2) (by simp) with h44335 | h44335
                                          · rcases p44331_3 (m.d 2 3) (by simp) with h44336 | h44336
                                            · linarith only [h44336, hlam, p44331_0]
                                            · rcases p44331_3 (m.d 2 4) (by simp) with h44338 | h44338
                                              · linarith only [h41028, h44338, hlam]
                                              · linarith only [h44274, h44338, hlam]
                                          · linarith only [h44268, h44335, hlam]
                                        · linarith only [h44334, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        rcases p44331_3 (m.d 0 2) (by simp) with h44343 | h44343
                                        · rcases p44331_3 (m.d 1 2) (by simp) with h44344 | h44344
                                          · rcases p44331_3 (m.d 2 3) (by simp) with h44345 | h44345
                                            · linarith only [h41027, h44345, hlam]
                                            · rcases p44331_3 (m.d 2 4) (by simp) with h44347 | h44347
                                              · linarith only [h44347, hlam, p44331_0]
                                              · rcases p44331_3 (m.d 2 5) (by simp) with h44349 | h44349
                                                · linarith only [h41029, h44349, hlam]
                                                · rcases h4bigk with h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c | h44351c
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h36828, hlam, p44351_1]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h41030, h44268, h44271, h44274, h44276, h44278, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44351_1]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h41030, hlam, p44351_1]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    rcases p44351_3 (m.d 0 4) (by simp) with h44356 | h44356
                                                    · rcases p44351_3 (m.d 1 4) (by simp) with h44357 | h44357
                                                      · rcases p44351_3 (m.d 2 4) (by simp) with h44358 | h44358
                                                        · linarith only [h41028, h44358, hlam]
                                                        · linarith only [h44277, h44358, hlam]
                                                      · linarith only [h44273, h44357, hlam]
                                                    · linarith only [h44356, hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    rcases p44351_3 (m.d 0 4) (by simp) with h44363 | h44363
                                                    · linarith only [h36828, h44363, hlam]
                                                    · rcases p44351_3 (m.d 1 4) (by simp) with h44365 | h44365
                                                      · rcases p44351_3 (m.d 2 4) (by simp) with h44366 | h44366
                                                        · linarith only [h44269, h44366, hlam]
                                                        · rcases p44351_3 (m.d 3 4) (by simp) with h44368 | h44368
                                                          · linarith only [h44271, h44368, hlam]
                                                          · linarith only [h41030, h44368, hlam]
                                                      · linarith only [h36828, h44365, hlam]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    rcases p44351_3 (m.d 0 4) (by simp) with h44373 | h44373
                                                    · linarith only [h36828, h44373, hlam]
                                                    · linarith only [h41028, h44373, hlam]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h41027, h41030, h44268, h44271, h44276, h44278, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44351_1]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    rcases p44351_3 (m.d 0 4) (by simp) with h44377 | h44377
                                                    · linarith only [h36828, h44377, hlam]
                                                    · linarith only [h44267, h44377, hlam]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h41028, hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h44269, hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h44274, hlam, p44351_1]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44331_1, p44351_1]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h36828, h44268, h44271, hc01, hc12, hlam, hphi, p44351_1]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h44271, hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h44268, h44271, h44274, h44276, h44278, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44351_1]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    rcases p44351_3 (m.d 0 4) (by simp) with h44389 | h44389
                                                    · linarith only [h41030, h44389, hlam]
                                                    · linarith only [h44267, h44389, hlam]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h44267, hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h44273, hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h44277, hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [h44278, hlam, p44351_0]
                                                  · have p44351_0 := h44351c.1
                                                    have p44351_1 := h44351c.2.1
                                                    have p44351_2 := h44351c.2.2.1
                                                    have p44351_3 := h44351c.2.2.2
                                                    linarith only [hlam, p44351_0]
                                          · linarith only [h44269, h44344, hlam]
                                        · linarith only [h44343, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        rcases p44331_3 (m.d 0 2) (by simp) with h44399 | h44399
                                        · rcases p44331_3 (m.d 1 2) (by simp) with h44400 | h44400
                                          · rcases p44331_3 (m.d 2 3) (by simp) with h44401 | h44401
                                            · linarith only [h41027, h44401, hlam]
                                            · linarith only [h44276, h44401, hlam]
                                          · linarith only [h44270, h44400, hlam]
                                        · linarith only [h44399, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h41027, h44276, h44278, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44331_1]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        rcases p44331_3 (m.d 0 2) (by simp) with h44408 | h44408
                                        · linarith only [h0, h44408, hlam]
                                        · linarith only [h41027, h44408, hlam]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        rcases p44331_3 (m.d 0 2) (by simp) with h44411 | h44411
                                        · linarith only [h0, h44411, hlam]
                                        · linarith only [h41028, h44411, hlam]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        rcases p44331_3 (m.d 0 2) (by simp) with h44414 | h44414
                                        · linarith only [h0, h44414, hlam]
                                        · linarith only [h41029, h44414, hlam]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h41027, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h44268, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h44274, hlam, p44331_1]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h41027, h41030, h44268, h44271, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p44331_1]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h41028, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h44269, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h41028, h41030, h44268, h44271, h44276, h44278, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44331_1]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        rcases p44331_3 (m.d 0 2) (by simp) with h44426 | h44426
                                        · rcases p44331_3 (m.d 1 2) (by simp) with h44427 | h44427
                                          · rcases p44331_3 (m.d 2 3) (by simp) with h44428 | h44428
                                            · linarith only [h44274, h44428, hlam]
                                            · linarith only [h44276, h44428, hlam]
                                          · linarith only [h44270, h44427, hlam]
                                        · linarith only [h41029, h44426, hlam]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h41029, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h44270, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h44276, hlam, p44331_0]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [h44277, hlam, p44331_1]
                                      · have p44331_0 := h44331c.1
                                        have p44331_1 := h44331c.2.1
                                        have p44331_2 := h44331c.2.2.1
                                        have p44331_3 := h44331c.2.2.2
                                        linarith only [hlam, p44331_0]
                                    · linarith only [h0, h44330, hc01, hlam]
                                    · linarith only [h41027, h41030, h44271, h44276, h44278, h44330, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h36828, h44330, hc01, hlam]
                                    · linarith only [h44330, hc01, hlam, p44279_1]
                                  · linarith only [h44329, hlam, p44279_0]
                                · linarith only [h36828, h44328, hlam]
                              · linarith only [h33187, h44327, hlam]
                            · linarith only [h0, h44326, hlam]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h44270, hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h44272, hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [h44273, hlam, p44279_0]
                        · have p44279_0 := h44279c.1
                          have p44279_1 := h44279c.2.1
                          have p44279_2 := h44279c.2.2.1
                          have p44279_3 := h44279c.2.2.2
                          linarith only [hlam, p44279_0]
                      · linarith only [h41027, h41030, h44267, h44276, h44278, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h41030, h44266, h44267, h44271, h44274, h44276, h44277, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h41030, h44266, h44268, h44271, h44276, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h36828, h41030, h44266, h44267, h44268, h44271, h44273, hc01, hc12, hlam, hphi]
            · linarith only [h41030, h44266, h44271, h44272, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h44455 | h44455
            · rcases m.htr 1 4 5 (by decide) (by decide) with h44456 | h44456
              · rcases m.htr 2 3 4 (by decide) (by decide) with h44457 | h44457
                · linarith only [h39227, h44271, h44455, h44457, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h44459 | h44459
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h44460 | h44460
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h44461 | h44461
                      · rcases h1bigk with h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c | h44462c
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h0, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h33187, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h36828, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h39227, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          rcases p44462_3 (m.d 0 1) (by simp) with h44468 | h44468
                          · linarith only [h44468, hlam, p44462_0]
                          · rcases p44462_3 (m.d 1 2) (by simp) with h44470 | h44470
                            · rcases p44462_3 (m.d 1 3) (by simp) with h44471 | h44471
                              · linarith only [h44268, h44471, hlam]
                              · linarith only [h33187, h44471, hlam]
                            · linarith only [h44470, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h39227, h44455, hc01, hc12, hlam, hphi, p44462_1]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h36828, hc01, hc12, hlam, hphi, p44462_1]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h39227, hc01, hc12, hlam, hphi, p44462_1]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h44271, hc01, hc34, hlam, hphi, ht12, ht23, p44462_1]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h44268, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h44271, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h39227, hc01, hc13, hlam, hphi, p44462_1]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          rcases p44462_3 (m.d 0 1) (by simp) with h44484 | h44484
                          · linarith only [h44484, hlam, p44462_0]
                          · rcases p44462_3 (m.d 1 2) (by simp) with h44486 | h44486
                            · rcases p44462_3 (m.d 1 3) (by simp) with h44487 | h44487
                              · linarith only [h44271, h44487, hlam]
                              · linarith only [h33187, h44487, hlam]
                            · linarith only [h0, h44486, hlam]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h44269, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h33187, h44271, hc01, hc34, hlam, hphi, ht12, ht23, p44462_1]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h39227, h44271, hc01, hc34, hlam, hphi, ht12, ht23, p44462_1]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h44271, h44455, hc01, hc34, hlam, hphi, ht12, ht23, p44462_1]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h44270, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h44455, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [h44456, hlam, p44462_0]
                        · have p44462_0 := h44462c.1
                          have p44462_1 := h44462c.2.1
                          have p44462_2 := h44462c.2.2.1
                          have p44462_3 := h44462c.2.2.2
                          linarith only [hlam, p44462_0]
                      · linarith only [h33187, h44271, h44461, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h44457, h44459, h44460, hlam]
                  · linarith only [h33187, h44266, h44271, h44459, hc23, hc34, hlam, hphi]
              · linarith only [h33187, h36828, h44266, h44267, h44271, h44456, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h33187, h44266, h44455, hlam]
        · linarith only [h0, h41029, h44270, hlam]
      · linarith only [h0, h41028, h44269, hlam]
    · linarith only [h0, h41027, h44268, hlam]
  · linarith only [h41030, h44266, h44267, hlam]

end R2N4
