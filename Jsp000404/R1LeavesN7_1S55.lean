import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S52
import Jsp000404.R1LeavesN7_1S54

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 1 3 4 (by decide) (by decide) with h18649 | h18649
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h0, h18447, h18648, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 1 2 5 (by decide) (by decide) with h18648 | h18648
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h0, h18446, h18647, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 1 2 4 (by decide) (by decide) with h18647 | h18647
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h0, h18445, h18646, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 1 2 3 (by decide) (by decide) with h18646 | h18646
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 4 5 (by decide) (by decide) with h18450 | h18450
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h15532, h18444, h18449, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 3 5 (by decide) (by decide) with h18449 | h18449
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h15532, h18443, h18448, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 3 4 (by decide) (by decide) with h18448 | h18448
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h0, h18444, h18447, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 5 (by decide) (by decide) with h18447 | h18447
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h15532, h18443, h18445, h18446, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 4 (by decide) (by decide) with h18446 | h18446
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 4 (by decide) (by decide) with h19547 | h19547
  · rcases m.htr 0 2 5 (by decide) (by decide) with h19548 | h19548
    · rcases m.htr 0 3 4 (by decide) (by decide) with h19549 | h19549
      · rcases m.htr 0 3 5 (by decide) (by decide) with h19550 | h19550
        · rcases m.htr 0 4 5 (by decide) (by decide) with h19551 | h19551
          · rcases m.htr 1 2 3 (by decide) (by decide) with h19552 | h19552
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19553 | h19553
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19554 | h19554
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19555 | h19555
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19556 | h19556
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19557 | h19557
                      · linarith only [h0, h18443, h18445, h19552, h19557, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h18443, h18445, h19551, h19552, h19557, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h18444, h18445, h19550, h19552, h19556, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h15532, h19549, h19555, hlam]
                · linarith only [h0, h18443, h18445, h19552, h19553, h19554, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h18443, h18445, h19552, h19553, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19564 | h19564
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19565 | h19565
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19566 | h19566
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19567 | h19567
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19568 | h19568
                      · linarith only [h0, h18443, h19552, h19568, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h18443, h19551, h19552, h19568, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h15532, h19550, h19567, hlam]
                  · linarith only [h15532, h19549, h19566, hlam]
                · linarith only [h0, h18444, h19548, h19565, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h19547, h19564, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h19575 | h19575
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19576 | h19576
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19577 | h19577
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19578 | h19578
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19579 | h19579
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19580 | h19580
                      · linarith only [h0, h18443, h18445, h19551, h19575, h19580, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19582 | h19582
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19583 | h19583
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h19584 | h19584
                            · linarith only [h18443, h19551, h19576, h19584, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h19586 | h19586
                              · linarith only [h18443, h19551, h19576, h19582, h19586, hlam]
                              · rcases h0bigk with h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c | h19588c
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h0, hlam, p19588_1]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h15532, hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h0, h18443, h18445, h19575, h19576, h19582, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19588_1]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h0, h18443, h18445, h19551, h19575, h19576, h19582, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19588_1]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h18445, h19575, hc01, hc12, hlam, hphi, p19588_1]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h18445, hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h18443, h18445, h19575, h19576, h19582, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19588_1]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h18443, h18445, h19551, h19575, h19576, h19582, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19588_1]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h18444, h18445, h19575, h19576, h19580, h19582, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19588_1]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h0, h18444, h18445, h19575, h19576, h19580, h19582, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19588_1]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  rcases p19588_3 (m.d 0 1) (by simp) with h19602 | h19602
                                  · linarith only [h15532, h19602, hlam]
                                  · linarith only [h18443, h19602, hlam]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  rcases p19588_3 (m.d 0 1) (by simp) with h19605 | h19605
                                  · linarith only [h15532, h19605, hlam]
                                  · linarith only [h18444, h19605, hlam]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h18443, hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h19547, hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h19549, hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h19551, hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h18444, hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h19548, hlam, p19588_1]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h19550, hlam, p19588_0]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [h0, h18443, h18444, h18445, h19575, h19576, h19582, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19588_1]
                                · have p19588_0 := h19588c.1
                                  have p19588_1 := h19588c.2.1
                                  have p19588_2 := h19588c.2.2.1
                                  have p19588_3 := h19588c.2.2.2
                                  linarith only [hlam, p19588_0]
                          · linarith only [h18445, h19550, h19583, hlam]
                        · linarith only [h18445, h19549, h19582, hlam]
                    · linarith only [h15532, h18444, h19550, h19579, hlam]
                  · linarith only [h18445, h19549, h19575, h19578, hlam]
                · linarith only [h0, h18445, h19575, h19577, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h18443, h18445, h19575, h19576, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19624 | h19624
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19625 | h19625
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19626 | h19626
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19627 | h19627
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19628 | h19628
                      · linarith only [h18443, h19551, h19628, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19630 | h19630
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19631 | h19631
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h19632 | h19632
                            · linarith only [h18443, h19551, h19624, h19632, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h19634 | h19634
                              · linarith only [h18443, h19551, h19624, h19630, h19634, hlam]
                              · rcases h0bigk with h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c | h19636c
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h0, hlam, p19636_1]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h15532, hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h0, h18443, h19575, h19624, h19630, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19636_1]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h0, h19575, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p19636_1]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h0, h19575, hc01, hc23, hlam, hphi, ht12, p19636_1]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h18445, hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  rcases p19636_3 (m.d 0 1) (by simp) with h19645 | h19645
                                  · linarith only [h0, h19645, hlam]
                                  · linarith only [h18443, h19645, hlam]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  rcases p19636_3 (m.d 0 1) (by simp) with h19648 | h19648
                                  · linarith only [h0, h19648, hlam]
                                  · linarith only [h18444, h19648, hlam]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  rcases p19636_3 (m.d 0 1) (by simp) with h19651 | h19651
                                  · linarith only [h15532, h19651, hlam]
                                  · rcases p19636_3 (m.d 0 2) (by simp) with h19653 | h19653
                                    · linarith only [h18445, h19653, hlam]
                                    · linarith only [h0, h19653, hlam]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  rcases p19636_3 (m.d 0 1) (by simp) with h19656 | h19656
                                  · linarith only [h15532, h19656, hlam]
                                  · rcases p19636_3 (m.d 0 2) (by simp) with h19658 | h19658
                                    · linarith only [h18445, h19658, hlam]
                                    · rcases p19636_3 (m.d 0 3) (by simp) with h19660 | h19660
                                      · rcases p19636_3 (m.d 0 4) (by simp) with h19661 | h19661
                                        · linarith only [h19549, h19661, hlam]
                                        · rcases p19636_3 (m.d 0 5) (by simp) with h19663 | h19663
                                          · linarith only [h19550, h19663, hlam]
                                          · rcases h2bigk with h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c | h19665c
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [hlam, p19665_0]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h0, hlam, p19665_1]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h18445, hlam, p19665_0]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h15532, h19575, h19630, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19636_1, p19665_1]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h15532, h19575, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p19636_1, p19665_1]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h19575, hc02, hc23, hlam, hphi, p19665_1]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [hlam, p19665_0]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h19575, hlam, p19665_0]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              rcases p19665_3 (m.d 0 2) (by simp) with h19674 | h19674
                                              · linarith only [h0, h19674, hlam]
                                              · linarith only [h19547, h19674, hlam]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              rcases p19665_3 (m.d 0 2) (by simp) with h19677 | h19677
                                              · linarith only [h0, h19677, hlam]
                                              · linarith only [h19548, h19677, hlam]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              rcases p19665_3 (m.d 0 2) (by simp) with h19680 | h19680
                                              · linarith only [h19680, hlam, p19665_0]
                                              · rcases p19665_3 (m.d 1 2) (by simp) with h19682 | h19682
                                                · linarith only [h19575, h19682, hlam]
                                                · linarith only [h0, h19682, hlam]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h0, h18444, h19624, h19628, h19630, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19665_1]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [hlam, p19665_0]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h0, h15532, h18444, h19575, h19624, h19628, hlam, p19636_1, p19665_2]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h15532, h19548, h19575, hlam, p19636_1, p19665_2]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h19547, hlam, p19665_0]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h19624, hlam, p19665_0]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h19630, hlam, p19665_1]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [hlam, p19665_0]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h19632, hlam, p19665_1]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h19548, hlam, p19665_0]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h19625, hlam, p19665_0]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h19631, hlam, p19665_1]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [h0, h18444, h19625, h19630, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p19636_1, p19665_1]
                                            · have p19665_0 := h19665c.1
                                              have p19665_1 := h19665c.2.1
                                              have p19665_2 := h19665c.2.2.1
                                              have p19665_3 := h19665c.2.2.2
                                              linarith only [hlam, p19665_0]
                                      · linarith only [h18445, h19660, hlam]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  rcases p19636_3 (m.d 0 1) (by simp) with h19701 | h19701
                                  · linarith only [h15532, h19701, hlam]
                                  · linarith only [h18443, h19701, hlam]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  rcases p19636_3 (m.d 0 1) (by simp) with h19704 | h19704
                                  · linarith only [h15532, h19704, hlam]
                                  · linarith only [h18444, h19704, hlam]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h18443, hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h19547, hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h19549, hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h19551, hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h18444, hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h19548, hlam, p19636_1]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h19550, hlam, p19636_0]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [h0, h18443, h18444, h19575, h19624, h19630, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19636_1]
                                · have p19636_0 := h19636c.1
                                  have p19636_1 := h19636c.2.1
                                  have p19636_2 := h19636c.2.2.1
                                  have p19636_3 := h19636c.2.2.2
                                  linarith only [hlam, p19636_0]
                          · linarith only [h0, h19575, h19631, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h18444, h19575, h19624, h19628, h19630, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h15532, h19550, h19627, hlam]
                  · linarith only [h15532, h19549, h19551, h19626, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h18443, h19548, h19624, h19625, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h19547, h19624, hlam]
        · linarith only [h15532, h18444, h19550, hlam]
      · linarith only [h0, h18443, h18445, h19549, hlam]
    · linarith only [h0, h18444, h19548, hlam]
  · linarith only [h0, h18443, h19547, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 3 (by decide) (by decide) with h18445 | h18445
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445

end R2N4
