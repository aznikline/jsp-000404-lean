import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S52
import Jsp000404.R1LeavesN7_1S53

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x12 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 3) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 3) ∧ (m.d 0 3) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 3) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x13 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 3) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 3) ∧ (m.d 0 4) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 4) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  rcases p18659_3 (m.d 0 1) (by simp) with h19240 | h19240
  · linarith only [h15532, h19240, hlam]
  · linarith only [h18443, h19240, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x14 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 3) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 3) ∧ (m.d 0 5) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 5) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  rcases p18659_3 (m.d 0 1) (by simp) with h19243 | h19243
  · linarith only [h15532, h19243, hlam]
  · linarith only [h18444, h19243, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x15 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 4) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 4) ∧ (m.d 0 1) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 1) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [h18443, hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x16 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 4) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 4) ∧ (m.d 0 2) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 2) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [h18446, hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x17 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 4) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 4) ∧ (m.d 0 3) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 3) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [h18448, hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x18 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 4) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 4) ∧ (m.d 0 4) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 4) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x19 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 4) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 4) ∧ (m.d 0 5) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 5) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [h18450, hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x20 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 5) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 5) ∧ (m.d 0 1) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 1) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [h18444, hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x21 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 5) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 5) ∧ (m.d 0 2) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 2) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [h18447, hlam, p18659_1]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x22 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 5) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 5) ∧ (m.d 0 3) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 3) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [h18449, hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x23 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 5) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 5) ∧ (m.d 0 4) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 4) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  rcases p18659_3 (m.d 0 1) (by simp) with h19254 | h19254
  · rcases p18659_3 (m.d 0 2) (by simp) with h19255 | h19255
    · rcases p18659_3 (m.d 0 3) (by simp) with h19256 | h19256
      · rcases p18659_3 (m.d 0 4) (by simp) with h19257 | h19257
        · linarith only [h18450, h19257, hlam]
        · rcases p18659_3 (m.d 0 5) (by simp) with h19259 | h19259
          · rcases h2bigk with h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c | h19260c
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h0, hlam, p19260_1]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              rcases p19260_3 (m.d 0 2) (by simp) with h19263 | h19263
              · rcases p19260_3 (m.d 1 2) (by simp) with h19264 | h19264
                · rcases p19260_3 (m.d 2 3) (by simp) with h19265 | h19265
                  · linarith only [h19265, hlam, p19260_0]
                  · rcases p19260_3 (m.d 2 4) (by simp) with h19267 | h19267
                    · linarith only [h18446, h19267, hlam]
                    · rcases p19260_3 (m.d 2 5) (by simp) with h19269 | h19269
                      · linarith only [h18447, h19269, hlam]
                      · rcases h3bigk with h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c | h19271c
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h15532, hlam, p19271_1]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          rcases p19271_3 (m.d 0 3) (by simp) with h19274 | h19274
                          · rcases p19271_3 (m.d 1 3) (by simp) with h19275 | h19275
                            · rcases p19271_3 (m.d 2 3) (by simp) with h19276 | h19276
                              · linarith only [h18445, h19276, hlam]
                              · rcases p19271_3 (m.d 3 4) (by simp) with h19278 | h19278
                                · linarith only [h18448, h19278, hlam]
                                · rcases p19271_3 (m.d 3 5) (by simp) with h19280 | h19280
                                  · linarith only [h18449, h19280, hlam]
                                  · rcases h5bigk with h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c | h19282c
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [hlam, p19282_0]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h0, h18444, h18648, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h15532, h18444, h18646, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h15532, h18444, h18646, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18450, hlam, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18444, hlam, p19282_0]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [hlam, p19282_0]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h15532, h18444, h18646, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h15532, h18444, h18646, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18651, hlam, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18447, hlam, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18648, hlam, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [hlam, p19282_0]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h0, h18447, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18655, hlam, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18449, hlam, p19282_0]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18650, hlam, p19282_0]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18654, hlam, p19282_0]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [hlam, p19282_0]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18657, hlam, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18443, h18647, h18653, hc34, hc45, hlam, hphi, p18659_1, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18647, h18651, h18653, hc34, hc45, hlam, hphi, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18653, h18655, hc34, hc45, hlam, hphi, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [h18657, hc34, hc45, hlam, hphi, p19282_1]
                                    · have p19282_0 := h19282c.1
                                      have p19282_1 := h19282c.2.1
                                      have p19282_2 := h19282c.2.2.1
                                      have p19282_3 := h19282c.2.2.2
                                      linarith only [hlam, p19282_0]
                            · linarith only [h18646, h19275, hlam]
                          · linarith only [h18445, h19274, hlam]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          rcases p19271_3 (m.d 0 3) (by simp) with h19310 | h19310
                          · rcases p19271_3 (m.d 1 3) (by simp) with h19311 | h19311
                            · rcases p19271_3 (m.d 2 3) (by simp) with h19312 | h19312
                              · linarith only [h18445, h19312, hlam]
                              · linarith only [h18653, h19312, hlam]
                            · linarith only [h18649, h19311, hlam]
                          · linarith only [h19310, hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          rcases p19271_3 (m.d 0 3) (by simp) with h19317 | h19317
                          · rcases p19271_3 (m.d 1 3) (by simp) with h19318 | h19318
                            · rcases p19271_3 (m.d 2 3) (by simp) with h19319 | h19319
                              · linarith only [h18445, h19319, hlam]
                              · linarith only [h18654, h19319, hlam]
                            · linarith only [h18650, h19318, hlam]
                          · linarith only [h19317, hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h15532, h18443, h18444, h18646, h18647, h18653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p19271_1]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          rcases p19271_3 (m.d 0 3) (by simp) with h19326 | h19326
                          · linarith only [h15532, h19326, hlam]
                          · linarith only [h18445, h19326, hlam]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h15532, h18443, h18444, h18647, h18653, hlam, p18659_1, p19271_2]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          rcases p19271_3 (m.d 0 3) (by simp) with h19330 | h19330
                          · linarith only [h15532, h19330, hlam]
                          · linarith only [h18449, h19330, hlam]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h18445, hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h18646, hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19260_1, p19271_1]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19260_1, p19271_1]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h18448, hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h18649, hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h18653, hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h18657, hlam, p19271_1]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h18449, hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h18650, hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h18654, hlam, p19271_0]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [h15532, h18444, h18650, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19271_1]
                        · have p19271_0 := h19271c.1
                          have p19271_1 := h19271c.2.1
                          have p19271_2 := h19271c.2.2.1
                          have p19271_3 := h19271c.2.2.2
                          linarith only [hlam, p19271_0]
                · linarith only [h18646, h19264, hlam]
              · linarith only [h19263, hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              rcases p19260_3 (m.d 0 2) (by simp) with h19350 | h19350
              · rcases p19260_3 (m.d 1 2) (by simp) with h19351 | h19351
                · rcases p19260_3 (m.d 2 3) (by simp) with h19352 | h19352
                  · linarith only [h18445, h19352, hlam]
                  · linarith only [h18653, h19352, hlam]
                · linarith only [h18647, h19351, hlam]
              · linarith only [h19350, hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              rcases p19260_3 (m.d 0 2) (by simp) with h19357 | h19357
              · rcases p19260_3 (m.d 1 2) (by simp) with h19358 | h19358
                · rcases p19260_3 (m.d 2 3) (by simp) with h19359 | h19359
                  · linarith only [h18445, h19359, hlam]
                  · linarith only [h18654, h19359, hlam]
                · linarith only [h18648, h19358, hlam]
              · linarith only [h19357, hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h0, h18443, h18444, h18647, h18653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p19260_1]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              rcases p19260_3 (m.d 0 2) (by simp) with h19366 | h19366
              · linarith only [h0, h19366, hlam]
              · linarith only [h18445, h19366, hlam]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h0, h18443, h18444, h18647, hlam, p18659_1, p19260_2]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              rcases p19260_3 (m.d 0 2) (by simp) with h19370 | h19370
              · linarith only [h0, h19370, hlam]
              · linarith only [h18447, h19370, hlam]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h18445, hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h18646, hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              rcases p19260_3 (m.d 0 2) (by simp) with h19376 | h19376
              · rcases p19260_3 (m.d 1 2) (by simp) with h19377 | h19377
                · rcases p19260_3 (m.d 2 3) (by simp) with h19378 | h19378
                  · rcases p19260_3 (m.d 2 4) (by simp) with h19379 | h19379
                    · linarith only [h18653, h19379, hlam]
                    · rcases p19260_3 (m.d 2 5) (by simp) with h19381 | h19381
                      · linarith only [h18654, h19381, hlam]
                      · linarith only [h18655, h19381, hlam]
                  · linarith only [h18653, h19378, hlam]
                · linarith only [h18647, h19377, hlam]
              · linarith only [h18446, h19376, hlam]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              rcases p19260_3 (m.d 0 2) (by simp) with h19387 | h19387
              · rcases p19260_3 (m.d 1 2) (by simp) with h19388 | h19388
                · rcases p19260_3 (m.d 2 3) (by simp) with h19389 | h19389
                  · rcases p19260_3 (m.d 2 4) (by simp) with h19390 | h19390
                    · linarith only [h18653, h19390, hlam]
                    · rcases p19260_3 (m.d 2 5) (by simp) with h19392 | h19392
                      · linarith only [h18654, h19392, hlam]
                      · rcases h3bigk with h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c | h19394c
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h15532, hlam, p19394_1]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18654, h18657, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p19260_1, p19394_1]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          rcases p19394_3 (m.d 0 3) (by simp) with h19398 | h19398
                          · rcases p19394_3 (m.d 1 3) (by simp) with h19399 | h19399
                            · rcases p19394_3 (m.d 2 3) (by simp) with h19400 | h19400
                              · linarith only [h18445, h19400, hlam]
                              · linarith only [h18653, h19400, hlam]
                            · linarith only [h18649, h19399, hlam]
                          · linarith only [h19398, hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          rcases p19394_3 (m.d 0 3) (by simp) with h19405 | h19405
                          · rcases p19394_3 (m.d 1 3) (by simp) with h19406 | h19406
                            · rcases p19394_3 (m.d 2 3) (by simp) with h19407 | h19407
                              · linarith only [h18445, h19407, hlam]
                              · linarith only [h18654, h19407, hlam]
                            · linarith only [h18650, h19406, hlam]
                          · linarith only [h19405, hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h15532, h18443, h18444, h18646, h18647, h18653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p19394_1]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18646, h18654, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19260_1, p19394_1]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h15532, h18443, h18444, h18647, h18653, hlam, p18659_1, p19394_2]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          rcases p19394_3 (m.d 0 3) (by simp) with h19416 | h19416
                          · linarith only [h15532, h19416, hlam]
                          · linarith only [h18449, h19416, hlam]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18445, hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18646, hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          rcases p19394_3 (m.d 0 3) (by simp) with h19422 | h19422
                          · rcases p19394_3 (m.d 1 3) (by simp) with h19423 | h19423
                            · rcases p19394_3 (m.d 2 3) (by simp) with h19424 | h19424
                              · rcases p19394_3 (m.d 3 4) (by simp) with h19425 | h19425
                                · linarith only [h19425, hlam, p19394_0]
                                · rcases p19394_3 (m.d 3 5) (by simp) with h19427 | h19427
                                  · linarith only [h18654, h19427, hlam]
                                  · linarith only [h18657, h19427, hlam]
                              · linarith only [h19424, hlam, p19394_0]
                            · linarith only [h18649, h19423, hlam]
                          · linarith only [h18448, h19422, hlam]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          rcases p19394_3 (m.d 0 3) (by simp) with h19433 | h19433
                          · rcases p19394_3 (m.d 1 3) (by simp) with h19434 | h19434
                            · rcases p19394_3 (m.d 2 3) (by simp) with h19435 | h19435
                              · rcases p19394_3 (m.d 3 4) (by simp) with h19436 | h19436
                                · linarith only [h18653, h19436, hlam]
                                · rcases p19394_3 (m.d 3 5) (by simp) with h19438 | h19438
                                  · linarith only [h19438, hlam, p19394_0]
                                  · rcases h5bigk with h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c | h19440c
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [hlam, p19440_0]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h15532, h18444, hc13, hc15, hlam, hphi, ht01, ht0b, ht5b, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h15532, h18444, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h15532, h18444, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18450, hlam, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18444, hlam, p19440_0]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [hlam, p19440_0]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h15532, h18444, h18646, h18654, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h15532, h18444, h18646, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18651, hlam, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18447, hlam, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18648, hlam, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [hlam, p19440_0]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h0, h18447, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18655, hlam, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18449, hlam, p19440_0]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18650, hlam, p19440_0]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18654, hlam, p19440_0]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [hlam, p19440_0]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18657, hlam, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18443, h18647, h18653, hc34, hc45, hlam, hphi, p18659_1, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18647, h18651, h18653, hc34, hc45, hlam, hphi, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18653, h18655, hc34, hc45, hlam, hphi, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [h18657, hc34, hc45, hlam, hphi, p19440_1]
                                    · have p19440_0 := h19440c.1
                                      have p19440_1 := h19440c.2.1
                                      have p19440_2 := h19440c.2.2.1
                                      have p19440_3 := h19440c.2.2.2
                                      linarith only [hlam, p19440_0]
                              · linarith only [h19435, hlam, p19394_0]
                            · linarith only [h18650, h19434, hlam]
                          · linarith only [h18449, h19433, hlam]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18448, hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18649, hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18653, hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18657, hlam, p19394_1]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18449, hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18650, hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h18654, hlam, p19394_0]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [h15532, h18444, h18646, h18650, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19394_1]
                        · have p19394_0 := h19394c.1
                          have p19394_1 := h19394c.2.1
                          have p19394_2 := h19394c.2.2.1
                          have p19394_3 := h19394c.2.2.2
                          linarith only [hlam, p19394_0]
                  · linarith only [h18654, h19389, hlam]
                · linarith only [h18648, h19388, hlam]
              · linarith only [h18447, h19387, hlam]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h18446, hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h18647, hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h18653, hlam, p19260_1]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h18655, hlam, p19260_1]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h18447, hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h18648, hlam, p19260_0]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h18654, hlam, p19260_1]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [h15532, h18444, h18646, h18648, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p19260_1]
            · have p19260_0 := h19260c.1
              have p19260_1 := h19260c.2.1
              have p19260_2 := h19260c.2.2.1
              have p19260_3 := h19260c.2.2.2
              linarith only [hlam, p19260_0]
          · linarith only [h18450, h19259, hlam]
      · linarith only [h18448, h19256, hlam]
    · linarith only [h18446, h19255, hlam]
  · linarith only [h18443, h19254, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x24 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 5) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 5) ∧ (m.d 0 5) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 5) ≤ z)))
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
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
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
  rcases h0bigk with h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c | h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x2 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x3 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x4 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x5 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x6 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x7 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x8 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x9 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x10 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x11 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x12 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x13 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x14 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x15 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x16 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x17 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x18 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x19 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x20 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x21 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x22 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x23 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x24 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657 h18659c

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  rcases m.htr 3 4 5 (by decide) (by decide) with h18657 | h18657
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655 h18657

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h18655 | h18655
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654 h18655

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x1 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  linarith only [h15532, h18444, h18646, h18650, h18653, h18654, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h18654 | h18654
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653 h18654

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h19498 | h19498
  · linarith only [h15532, h18443, h18646, h18649, h18653, h19498, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h19500 | h19500
    · linarith only [h0, h18443, h18446, h18450, h18649, h18653, h19500, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h19502 | h19502
      · linarith only [h18443, h18450, h18649, h19502, hlam]
      · rcases h0bigk with h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c | h19504c
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h0, hlam, p19504_1]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h15532, hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h15532, h18443, h18646, h18649, h18653, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19504_1]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h15532, h18443, h18450, h18646, h18649, h18653, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19504_1]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h0, h18443, h18649, h18653, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19504_1]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h0, h15532, h18444, h18649, h18651, h18653, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19504_1]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          rcases p19504_3 (m.d 0 1) (by simp) with h19513 | h19513
          · linarith only [h0, h19513, hlam]
          · linarith only [h18443, h19513, hlam]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          rcases p19504_3 (m.d 0 1) (by simp) with h19516 | h19516
          · linarith only [h0, h19516, hlam]
          · linarith only [h18444, h19516, hlam]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h18444, h18649, h18651, h18653, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19504_1]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h18445, hlam, p19504_1]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          rcases p19504_3 (m.d 0 1) (by simp) with h19522 | h19522
          · linarith only [h15532, h19522, hlam]
          · linarith only [h18443, h19522, hlam]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          rcases p19504_3 (m.d 0 1) (by simp) with h19525 | h19525
          · linarith only [h15532, h19525, hlam]
          · linarith only [h18444, h19525, hlam]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h18443, hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h18446, hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h18448, hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h18450, hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h18444, hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h18447, hlam, p19504_1]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h18449, hlam, p19504_0]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [h0, h18443, h18444, h18649, h18653, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19504_1]
        · have p19504_0 := h19504c.1
          have p19504_1 := h19504c.2.1
          have p19504_2 := h19504c.2.2.1
          have p19504_3 := h19504c.2.2.2
          linarith only [hlam, p19504_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h18653 | h18653
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651 h18653

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  rcases m.htr 1 4 5 (by decide) (by decide) with h18651 | h18651
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650 h18651

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  linarith only [h15532, h18449, h18650, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0 (m : N7Model)
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
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h18650 | h18650
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h18445 h18446 h18447 h18448 h18449 h18450 h18646 h18647 h18648 h18649 h18650

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x1 (m : N7Model)
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
    (h18649 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  linarith only [h15532, h18448, h18649, hlam]

end R2N4
