import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_40S9
import Jsp000404.R1LeavesN7_40S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6940000 in
set_option maxHeartbeats 6940000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2572 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2574 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2576 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2578 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h3425 | h3425
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3426 | h3426
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3427 | h3427
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3428 | h3428
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3429 | h3429
          · linarith only [h0, h2578, h3429, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h3429, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3432 | h3432
          · linarith only [h2574, h2578, h3425, h3428, h3432, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h3432, hc23, hlam, hphi, ht12, u1ehi0]
      · linarith only [h2578, h3425, h3427, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3436 | h3436
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3437 | h3437
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3438 | h3438
          · linarith only [h0, h2578, h3438, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h3438, hc23, hlam, hphi, ht12, u1ehi0]
        · linarith only [h2578, h3425, h3426, h3437, hlam]
      · linarith only [h2578, h3425, h3436, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3443 | h3443
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3444 | h3444
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3445 | h3445
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3446 | h3446
          · linarith only [h0, h2578, h3446, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h3446, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3449 | h3449
          · linarith only [h0, h2578, h3449, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h3449, hc23, hlam, hphi, ht12, u1ehi0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3452 | h3452
        · linarith only [h3443, h3444, h3452, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3454 | h3454
          · linarith only [h0, h2578, h3454, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h3454, hc23, hlam, hphi, ht12, u1ehi0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3457 | h3457
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3458 | h3458
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3459 | h3459
          · linarith only [h0, h2578, h3459, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h3459, hc23, hlam, hphi, ht12, u1ehi0]
        · linarith only [h3443, h3457, h3458, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3463 | h3463
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3464 | h3464
          · linarith only [h0, h2578, h3464, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h3464, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3467 | h3467
          · linarith only [h0, h2578, h3467, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h3467, hc23, hlam, hphi, ht12, u1ehi0]

set_option maxHeartbeats 6940000 in
set_option maxHeartbeats 6940000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2572 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2574 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2576 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2578 | h2578
  · exact r1l7_11_13_25_L_R_L_I_H_I_x1_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h2572 h2574 h2576 h2578
  · exact r1l7_11_13_25_L_R_L_I_H_I_x1_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h2572 h2574 h2576 h2578

set_option maxHeartbeats 6940000 in
set_option maxHeartbeats 6940000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2572 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2574 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2576 | h2576
  · exact r1l7_11_13_25_L_R_L_I_H_I_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h2572 h2574 h2576
  · exact r1l7_11_13_25_L_R_L_I_H_I_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h2572 h2574 h2576

set_option maxHeartbeats 6940000 in
set_option maxHeartbeats 6940000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2572 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2574 | h2574
  · exact r1l7_11_13_25_L_R_L_I_H_I_x1_x1_x0 m hb1 hb3 hb5 h0 h2572 h2574
  · exact r1l7_11_13_25_L_R_L_I_H_I_x1_x1_x1 m hb1 hb3 hb5 h0 h2572 h2574

set_option maxHeartbeats 6940000 in
set_option maxHeartbeats 6940000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h2572 | h2572
  · exact r1l7_11_13_25_L_R_L_I_H_I_x1_x0 m hb1 hb3 hb5 h0 h2572
  · exact r1l7_11_13_25_L_R_L_I_H_I_x1_x1 m hb1 hb3 hb5 h0 h2572

set_option maxHeartbeats 6940000 in
set_option maxHeartbeats 6940000 in
theorem r1l7_11_13_25_L_R_L_I_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_R_L_I_H_I_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_R_L_I_H_I_x1 m hb1 hb3 hb5 h0

set_option maxHeartbeats 6854000 in
set_option maxHeartbeats 6854000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                              · linarith only [h0, h10, h16, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h0, h10, h13, h16, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h15, h9, hc14, hlam, hphi, u4elo0]
                          · linarith only [h0, h13, h14, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h0, h13, h21, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                              · linarith only [h0, h13, h24, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                                · linarith only [h10, h21, h26, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                                  · linarith only [h0, h11, h28, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h23, h28, hc24, hlam, hphi, u4elo1]
                            · linarith only [h23, h9, hc14, hlam, hphi, u4elo0]
                      · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h10, h11, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
                    · linarith only [h0, h10, h34, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                      · linarith only [h0, h10, h36, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                                    · linarith only [h1, h38, h44, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h40, h44, hc34, hlam, hphi, u4elo1]
                                  · linarith only [h34, h40, h43, hlam]
                                · linarith only [h10, h39, h42, hlam]
                              · linarith only [h0, h10, h39, h4, h41, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h40, h9, hc14, hlam, hphi, u4elo0]
                          · linarith only [h0, h38, h39, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                          · linarith only [h0, h38, h4, h52, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                              · linarith only [h0, h10, h38, h4, h55, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h10, h55, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h54, h9, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                            · linarith only [h64, h9, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                              · linarith only [h0, h59, h66, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h1, h62, h66, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h4, h62, h63, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h62, h7, h9, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h59, h6, h61, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h59, h60, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                    · linarith only [h0, h4, h59, h73, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h5, h73, h9, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
                · linarith only [h7, h76, h8, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h82 | h82
                          · linarith only [h1, h8, h82, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                            · linarith only [h76, h84, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                              · linarith only [h0, h78, h86, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h1, h8, h81, h86, hc23, hc35, hlam, hphi]
                        · linarith only [h7, h76, h8, h81, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h6, h78, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h78, h79, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
                    · linarith only [h0, h4, h78, h92, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h5, h76, h92, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h95 | h95
              · rcases m.htr 0 4 5 (by decide) (by decide) with h96 | h96
                · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                        · linarith only [h1, h100, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                              · linarith only [h0, h104, h4, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                                · linarith only [h0, h106, h97, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h1, h102, h106, h7, hc23, hlam, hphi, ht34, u4elo3]
                            · linarith only [h100, h102, h103, h96, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h102, h7, h95, hc13, hlam, hphi, ht34, u4elo3]
                      · linarith only [h0, h6, h97, h99, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h97, h98, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h4, h7, h97, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h7, h95, h96, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h115 | h115
                · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                        · linarith only [h1, h119, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                          · linarith only [h119, h121, h95, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                              · linarith only [h0, h116, h124, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                                · linarith only [h1, h116, h126, h95, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h128 | h128
                                  · linarith only [h0, h117, h128, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h123, h128, h2, hc24, hlam, hphi, u4elo0]
                            · linarith only [h115, h123, h7, hc14, hlam, hphi, u4elo3]
                      · linarith only [h0, h116, h118, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h116, h117, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h116, h4, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                        · linarith only [h1, h115, h138, h7, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
                          · linarith only [h138, h140, h95, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h142 | h142
                            · linarith only [h115, h142, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                              · linarith only [h1, h135, h144, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                                · linarith only [h1, h135, h146, h95, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h148 | h148
                                  · linarith only [h115, h148, hc04, hlam, hphi, u4elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h150 | h150
                                    · linarith only [h1, h115, h135, h150, h7, hc23, hlam, hphi, ht34, u4elo3]
                                    · linarith only [h1, h135, h150, h7, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h135, h137, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h135, h136, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h115, h135, h4, h7, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h156 | h156
            · rcases m.htr 0 3 5 (by decide) (by decide) with h157 | h157
              · linarith only [h157, h4, h6, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h159 | h159
                · linarith only [h159, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h163 | h163
                      · linarith only [h0, h163, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h165 | h165
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h166 | h166
                          · linarith only [h1, h157, h166, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h168 | h168
                            · linarith only [h159, h168, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h170 | h170
                              · linarith only [h0, h161, h170, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h156, h159, h170, h4, h6, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h156, h159, h165, h4, h6, hc13, hlam, hphi, ht34, u4elo4]
                    · linarith only [h159, h162, h5, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h159, h161, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h176 | h176
              · linarith only [h176, h4, h6, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                · linarith only [h178, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                      · linarith only [h0, h182, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
                        · linarith only [h1, h156, h184, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
                          · linarith only [h1, h176, h186, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h188 | h188
                            · linarith only [h178, h188, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                              · linarith only [h0, h156, h180, h190, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                                · linarith only [h1, h176, h180, h192, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h194 | h194
                                  · linarith only [h178, h181, h182, h194, h3, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                  · linarith only [h0, h181, h190, h194, h6, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h181, h5, h6, hc12, hc25, hlam, hphi]
                  · linarith only [h178, h180, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h200 | h200
        · rcases m.htr 0 2 5 (by decide) (by decide) with h201 | h201
          · rcases m.htr 0 3 4 (by decide) (by decide) with h202 | h202
            · rcases m.htr 0 3 5 (by decide) (by decide) with h203 | h203
              · rcases m.htr 0 4 5 (by decide) (by decide) with h204 | h204
                · rcases m.htr 1 2 3 (by decide) (by decide) with h205 | h205
                  · linarith only [h0, h200, h205, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h207 | h207
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h208 | h208
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h209 | h209
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h211 | h211
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h213 | h213
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h214 | h214
                                  · linarith only [h0, h207, h214, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h2, h211, h212, h214, hc34, hlam, hphi, u4elo0]
                                · linarith only [h203, h213, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h212, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h204, h211, hc14, hlam, hphi, u4elo0]
                          · linarith only [h1, h203, h205, h207, h210, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h205, h207, h209, hc24, hlam, hphi, u4elo3]
                      · linarith only [h201, h207, h208, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h200, h207, h4, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                  · linarith only [h0, h224, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h226 | h226
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h227 | h227
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h228 | h228
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h230 | h230
                            · linarith only [h204, h230, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h233 | h233
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h234 | h234
                                  · linarith only [h2, h204, h226, h234, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h236 | h236
                                    · linarith only [h2, h204, h226, h232, h236, hlam]
                                    · rcases h0bigk with h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h0, h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p238_1, u0elo0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h1, h224, h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p238_1, u0elo0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        rcases p238_3 (m.d 0 1) (by simp) with h242 | h242
                                        · rcases p238_3 (m.d 0 2) (by simp) with h243 | h243
                                          · linarith only [h0, h243, hlam]
                                          · linarith only [h200, h243, hlam]
                                        · linarith only [h2, h242, hlam]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        rcases p238_3 (m.d 0 1) (by simp) with h247 | h247
                                        · rcases p238_3 (m.d 0 2) (by simp) with h248 | h248
                                          · linarith only [h0, h248, hlam]
                                          · linarith only [h201, h248, hlam]
                                        · linarith only [h247, h3, hlam]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h0, hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h4, hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        rcases p238_3 (m.d 0 1) (by simp) with h255 | h255
                                        · rcases p238_3 (m.d 0 2) (by simp) with h256 | h256
                                          · rcases p238_3 (m.d 0 3) (by simp) with h257 | h257
                                            · rcases p238_3 (m.d 0 4) (by simp) with h258 | h258
                                              · linarith only [h200, h258, hlam]
                                              · rcases p238_3 (m.d 0 5) (by simp) with h260 | h260
                                                · linarith only [h201, h260, hlam]
                                                · linarith only [h204, h260, hlam]
                                            · linarith only [h202, h257, hlam]
                                          · linarith only [h200, h256, hlam]
                                        · linarith only [h2, h255, hlam]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        rcases p238_3 (m.d 0 1) (by simp) with h266 | h266
                                        · rcases p238_3 (m.d 0 2) (by simp) with h267 | h267
                                          · rcases p238_3 (m.d 0 3) (by simp) with h268 | h268
                                            · rcases p238_3 (m.d 0 4) (by simp) with h269 | h269
                                              · linarith only [h200, h269, hlam]
                                              · rcases p238_3 (m.d 0 5) (by simp) with h271 | h271
                                                · linarith only [h201, h271, hlam]
                                                · rcases h0emin with h273 | h273 | h273 | h273 | h273
                                                  · rcases h1bigk with h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p274_1, u0elo0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h224, h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p274_1, u0elo0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      rcases p274_3 (m.d 0 1) (by simp) with h278 | h278
                                                      · rcases p274_3 (m.d 1 2) (by simp) with h279 | h279
                                                        · linarith only [h0, h279, hlam]
                                                        · linarith only [h226, h279, hlam]
                                                      · linarith only [h278, hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      rcases p274_3 (m.d 0 1) (by simp) with h283 | h283
                                                      · rcases p274_3 (m.d 1 2) (by simp) with h284 | h284
                                                        · linarith only [h0, h284, hlam]
                                                        · linarith only [h227, h284, hlam]
                                                      · linarith only [h283, hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h0, hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h224, hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h0, h226, h232, hc34, hlam, hphi, ht0b, ht45, ht5b, p274_1, u0elo0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h1, h224, h226, h230, h232, hc34, hlam, hphi, ht0b, ht45, ht5b, p274_1, u0elo0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h1, hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h1, h2, h204, h226, h232, h4, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p238_1, p274_1, u0elo0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h1, h226, h232, hc34, hlam, hphi, ht0b, ht45, ht5b, p274_1, u0elo0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h1, h226, h230, h232, hc34, hlam, hphi, ht0b, ht45, ht5b, p274_1, u0elo0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h2, hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h226, hlam, p274_1]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h228, hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h230, hlam, p274_1]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h3, hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h227, hlam, p274_1]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h229, hlam, p274_0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [h226, h232, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p274_1, u0elo0]
                                                    · have p274_0 := h274c.1
                                                      have p274_1 := h274c.2.1
                                                      have p274_2 := h274c.2.2.1
                                                      have p274_3 := h274c.2.2.2
                                                      linarith only [hlam, p274_0]
                                                  · rcases h1bigk with h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p308_1, u0elo0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h224, h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p308_1, u0elo0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      rcases p308_3 (m.d 0 1) (by simp) with h312 | h312
                                                      · rcases p308_3 (m.d 1 2) (by simp) with h313 | h313
                                                        · linarith only [h0, h313, hlam]
                                                        · linarith only [h226, h313, hlam]
                                                      · linarith only [h312, hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      rcases p308_3 (m.d 0 1) (by simp) with h317 | h317
                                                      · rcases p308_3 (m.d 1 2) (by simp) with h318 | h318
                                                        · linarith only [h0, h318, hlam]
                                                        · linarith only [h227, h318, hlam]
                                                      · linarith only [h317, hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h0, hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h224, hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h0, h226, h232, hc34, hlam, hphi, ht0b, ht45, ht5b, p308_1, u0elo0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h1, h224, hc15, hlam, hphi, ht0b, ht5b, p308_1, u0elo0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h1, hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h1, h2, h204, h226, h232, h4, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p238_1, p308_1, u0elo0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h1, h226, h232, hc34, hlam, hphi, ht0b, ht45, ht5b, p308_1, u0elo0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h1, h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p308_1, u0elo0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h2, hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h226, hlam, p308_1]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h228, hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h230, hlam, p308_1]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h3, hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h227, hlam, p308_1]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h229, hlam, p308_0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [h226, h232, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p308_1, u0elo0]
                                                    · have p308_0 := h308c.1
                                                      have p308_1 := h308c.2.1
                                                      have p308_2 := h308c.2.2.1
                                                      have p308_3 := h308c.2.2.2
                                                      linarith only [hlam, p308_0]
                                                  · rcases h1bigk with h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p342_1, u0elo0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h224, h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p342_1, u0elo0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      rcases p342_3 (m.d 0 1) (by simp) with h346 | h346
                                                      · rcases p342_3 (m.d 1 2) (by simp) with h347 | h347
                                                        · linarith only [h0, h347, hlam]
                                                        · linarith only [h226, h347, hlam]
                                                      · linarith only [h346, hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      rcases p342_3 (m.d 0 1) (by simp) with h351 | h351
                                                      · rcases p342_3 (m.d 1 2) (by simp) with h352 | h352
                                                        · linarith only [h0, h352, hlam]
                                                        · linarith only [h227, h352, hlam]
                                                      · linarith only [h351, hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h0, hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h224, hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h0, h226, h232, hc34, hlam, hphi, ht0b, ht45, ht5b, p342_1, u0elo0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h1, h224, hc15, hlam, hphi, ht0b, ht5b, p342_1, u0elo0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h1, hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h1, h2, h204, h226, h232, h4, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p238_1, p342_1, u0elo0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h1, h226, h232, hc34, hlam, hphi, ht0b, ht45, ht5b, p342_1, u0elo0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h1, h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p342_1, u0elo0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h2, hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h226, hlam, p342_1]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h228, hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h230, hlam, p342_1]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h3, hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h227, hlam, p342_1]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h229, hlam, p342_0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [h226, h232, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p342_1, u0elo0]
                                                    · have p342_0 := h342c.1
                                                      have p342_1 := h342c.2.1
                                                      have p342_2 := h342c.2.2.1
                                                      have p342_3 := h342c.2.2.2
                                                      linarith only [hlam, p342_0]
                                                  · linarith only [h204, h273, h4, hc23, hlam, ht01, ht12, p238_1]
                                                  · linarith only [h273, h4, hc23, hlam, ht01, ht12, p238_1]
                                            · linarith only [h203, h268, hlam]
                                          · linarith only [h201, h267, hlam]
                                        · linarith only [h266, h3, hlam]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h1, hlam, p238_1]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h0, h227, h232, h234, hc34, hlam, hphi, ht0b, ht45, ht5b, p238_1, u0elo2]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        rcases p238_3 (m.d 0 1) (by simp) with h384 | h384
                                        · rcases p238_3 (m.d 0 2) (by simp) with h385 | h385
                                          · linarith only [h385, h4, hlam]
                                          · linarith only [h200, h385, hlam]
                                        · linarith only [h2, h384, hlam]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        rcases p238_3 (m.d 0 1) (by simp) with h389 | h389
                                        · rcases p238_3 (m.d 0 2) (by simp) with h390 | h390
                                          · linarith only [h390, h4, hlam]
                                          · linarith only [h201, h390, hlam]
                                        · linarith only [h3, h389, hlam]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h2, hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h200, hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h202, hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h204, hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h3, hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h201, hlam, p238_1]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h203, hlam, p238_0]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [h2, h204, h226, h232, hc34, hlam, hphi, p238_1, u4elo4]
                                      · have p238_0 := h238c.1
                                        have p238_1 := h238c.2.1
                                        have p238_2 := h238c.2.2.1
                                        have p238_3 := h238c.2.2.2
                                        linarith only [hlam, p238_0]
                                · linarith only [h203, h233, h4, hlam]
                              · linarith only [h232, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h1, h203, h224, h226, h229, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h224, h226, h228, hc24, hlam, hphi, u4elo3]
                      · linarith only [h201, h226, h227, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h200, h226, h4, hc12, hc23, hlam, hphi]
              · linarith only [h201, h203, h4, hlam]
            · linarith only [h200, h202, h4, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h412 | h412
            · rcases m.htr 0 3 5 (by decide) (by decide) with h413 | h413
              · rcases m.htr 0 4 5 (by decide) (by decide) with h414 | h414
                · linarith only [h200, h201, h414, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
                  · linarith only [h0, h4, h416, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h419 | h419
                      · linarith only [h0, h201, h419, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h421 | h421
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h422 | h422
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h423 | h423
                            · linarith only [h414, h423, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h425 | h425
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h426 | h426
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h427 | h427
                                  · linarith only [h0, h414, h418, h427, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h0, h201, h418, h427, hc24, hlam, hphi, u4elo4]
                                · linarith only [h1, h422, h426, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h0, h4, h418, h425, hc24, hlam, hphi, u4elo3]
                          · linarith only [h1, h413, h416, h418, h422, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h416, h418, h421, hc24, hlam, hphi, u4elo3]
                    · linarith only [h200, h201, h418, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h435 | h435
                · linarith only [h200, h4, h413, h435, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
                  · linarith only [h0, h4, h437, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
                      · linarith only [h0, h201, h440, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h443 | h443
                          · linarith only [h0, h1, h4, h413, h439, h443, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
                            · linarith only [h2, h435, h445, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h449 | h449
                                  · linarith only [h0, h4, h413, h435, h439, h448, h449, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h4, h413, h439, h448, h449, hc24, hlam, hphi, u4elo4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                                  · linarith only [h0, h4, h439, h448, h452, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                  · linarith only [h0, h201, h439, h447, h452, hc34, hlam, hphi, u4elo4]
                              · linarith only [h4, h447, hc02, hlam, hphi, ht23, ht34, u4elo3]
                        · linarith only [h412, h413, h442, hc13, hc35, hlam, hphi]
                    · linarith only [h200, h4, h439, hc12, hc23, hlam, hphi]
            · linarith only [h200, h4, h412, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h459 | h459
          · rcases m.htr 0 3 4 (by decide) (by decide) with h460 | h460
            · rcases m.htr 0 3 5 (by decide) (by decide) with h461 | h461
              · rcases m.htr 0 4 5 (by decide) (by decide) with h462 | h462
                · rcases m.htr 1 2 3 (by decide) (by decide) with h463 | h463
                  · linarith only [h0, h200, h463, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h465 | h465
                    · linarith only [h0, h200, h465, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h467 | h467
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h468 | h468
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h469 | h469
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h470 | h470
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h471 | h471
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h472 | h472
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h473 | h473
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h474 | h474
                                    · linarith only [h1, h468, h474, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h462, h474, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h0, h200, h467, h470, h473, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h200, h461, h467, h471, h472, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h0, h4, h467, h471, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                            · linarith only [h462, h470, hc14, hlam, hphi, u4elo0]
                          · linarith only [h461, h468, h469, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h460, h463, h467, h468, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h200, h459, h467, hc12, hlam, hphi, ht23, ht34, u4elo2]
                · linarith only [h200, h459, h462, hlam]
              · linarith only [h4, h459, h461, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h486 | h486
              · rcases m.htr 0 4 5 (by decide) (by decide) with h487 | h487
                · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                  · linarith only [h0, h4, h459, h488, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                    · linarith only [h0, h4, h460, h490, hc24, hlam, hphi, u4elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                        · linarith only [h0, h1, h4, h460, h492, h493, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h496 | h496
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h497 | h497
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h498 | h498
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h499 | h499
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h500 | h500
                                    · rcases h0bigk with h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c | h501c
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, h492, h498, h500, hc45, hlam, hphi, ht0b, ht5b, p501_1, u0elo0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, h4, h492, h498, h500, hc45, hlam, hphi, ht0b, ht5b, p501_1, u0elo0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, h4, h460, h492, h498, h500, hc45, hlam, hphi, ht0b, ht5b, p501_1, u0elo0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        rcases p501_3 (m.d 0 1) (by simp) with h506 | h506
                                        · rcases p501_3 (m.d 0 2) (by simp) with h507 | h507
                                          · linarith only [h0, h507, hlam]
                                          · linarith only [h459, h507, hlam]
                                        · linarith only [h3, h506, hlam]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h4, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h200, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h4, h460, h497, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p501_1, u4elo2]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h1, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h460, h497, hc02, hlam, hphi, ht23, ht34, p501_1, u4elo2]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h460, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h459, h460, h497, h498, h500, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p501_1, u4elo2]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h2, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h0, h492, h498, h500, hc45, hlam, hphi, ht0b, ht5b, p501_1, u0elo3]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h460, h497, hc03, hlam, hphi, ht34, p501_1, u4elo2]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        rcases p501_3 (m.d 0 1) (by simp) with h525 | h525
                                        · rcases p501_3 (m.d 0 2) (by simp) with h526 | h526
                                          · linarith only [h200, h526, hlam]
                                          · linarith only [h459, h526, hlam]
                                        · linarith only [h3, h525, hlam]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h3, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h459, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h486, hlam, p501_0]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [h487, hlam, p501_1]
                                      · have p501_0 := h501c.1
                                        have p501_1 := h501c.2.1
                                        have p501_2 := h501c.2.2.1
                                        have p501_3 := h501c.2.2.2
                                        linarith only [hlam, p501_0]
                                    · linarith only [h460, h500, hc03, hlam, hphi, ht34, u4elo4]
                                  · linarith only [h200, h499, hc02, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h4, h460, h497, h498, hc02, hc35, hlam, hphi, ht23]
                              · linarith only [h4, h497, hc02, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h200, h487, h496, hc14, hlam, hphi, u4elo2]
                          · linarith only [h460, h486, h495, hc13, hlam, hphi, ht34, u4elo3]
                      · linarith only [h4, h459, h460, h492, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h4, h459, h460, h487, hlam]
              · linarith only [h4, h459, h486, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h544 | h544
            · rcases m.htr 0 3 5 (by decide) (by decide) with h545 | h545
              · rcases m.htr 0 4 5 (by decide) (by decide) with h546 | h546
                · rcases m.htr 1 2 3 (by decide) (by decide) with h547 | h547
                  · linarith only [h0, h4, h547, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h549 | h549
                    · linarith only [h0, h200, h549, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h551 | h551
                      · linarith only [h0, h459, h551, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h553 | h553
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h554 | h554
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h555 | h555
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h556 | h556
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h557 | h557
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h558 | h558
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h559 | h559
                                    · linarith only [h1, h553, h559, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h546, h559, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h200, h555, h558, hc04, hlam, hphi, u4elo1]
                                · linarith only [h0, h1, h200, h554, h556, h557, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h4, h556, hc02, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h546, h555, hc14, hlam, hphi, u4elo0]
                          · linarith only [h545, h553, h554, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h567 | h567
                          · linarith only [h1, h544, h553, h567, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h569 | h569
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h570 | h570
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h571 | h571
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h572 | h572
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h573 | h573
                                    · rcases h0bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        rcases p574_3 (m.d 0 1) (by simp) with h576 | h576
                                        · rcases p574_3 (m.d 0 2) (by simp) with h577 | h577
                                          · linarith only [h0, h577, hlam]
                                          · rcases p574_3 (m.d 0 3) (by simp) with h579 | h579
                                            · linarith only [h1, h579, hlam]
                                            · linarith only [h4, h579, hlam]
                                        · linarith only [h0, h576, hlam]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h544, h547, h567, h573, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p574_1, u0elo0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h2, h569, hc45, hlam, hphi, ht0b, ht5b, p574_1, u0elo0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h545, h547, h567, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p574_1, u0elo0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h0, hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h4, hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h200, hlam, p574_1]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h459, hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h1, hlam, p574_1]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        rcases p574_3 (m.d 0 1) (by simp) with h592 | h592
                                        · rcases p574_3 (m.d 0 2) (by simp) with h593 | h593
                                          · linarith only [h4, h593, hlam]
                                          · rcases p574_3 (m.d 0 3) (by simp) with h595 | h595
                                            · rcases p574_3 (m.d 0 4) (by simp) with h596 | h596
                                              · linarith only [h544, h596, hlam]
                                              · linarith only [h200, h596, hlam]
                                            · linarith only [h4, h595, hlam]
                                        · linarith only [h0, h592, hlam]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h544, h547, h567, h573, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p574_1, u0elo2]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h1, h545, h547, h567, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p574_1, u0elo0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h2, hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, p574_1, u4elo0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h544, hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h200, h545, h547, h567, hc12, hlam, hphi, ht23, ht34, p574_1, u4elo2]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h3, hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h0, h200, h546, hc12, hlam, hphi, ht23, ht34, p574_1, u4elo2]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h545, hlam, p574_0]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [h546, hlam, p574_1]
                                      · have p574_0 := h574c.1
                                        have p574_1 := h574c.2.1
                                        have p574_2 := h574c.2.2.1
                                        have p574_3 := h574c.2.2.2
                                        linarith only [hlam, p574_0]
                                    · linarith only [h569, h573, hc34, hlam, hphi, u4elo1]
                                  · linarith only [h200, h3, h546, h569, h572, hlam]
                                · linarith only [h0, h4, h545, h546, h571, hc12, hlam, hphi, ht23, ht34, u4elo0]
                              · linarith only [h4, h544, h570, hlam]
                            · linarith only [h200, h546, h569, hc14, hlam, hphi, u4elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h619 | h619
                  · linarith only [h0, h4, h545, h619, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h621 | h621
                    · linarith only [h0, h200, h546, h621, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h623 | h623
                      · linarith only [h0, h459, h623, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h625 | h625
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h626 | h626
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h627 | h627
                            · linarith only [h200, h546, h627, hc02, hlam, hphi, ht23, ht34, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h629 | h629
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h630 | h630
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h631 | h631
                                  · linarith only [h0, h200, h546, h631, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                  · linarith only [h0, h200, h631, hc12, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h0, h200, h545, h629, h630, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h1, h4, h625, h629, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h1, h545, h625, h626, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h544, h546, h625, hc13, hlam, hphi, ht34, u4elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h638 | h638
                · linarith only [h544, h545, h638, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h640 | h640
                  · linarith only [h0, h4, h640, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h642 | h642
                    · linarith only [h0, h200, h642, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h644 | h644
                      · linarith only [h0, h459, h644, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h646 | h646
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h647 | h647
                          · linarith only [h1, h545, h647, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h649 | h649
                            · linarith only [h2, h638, h649, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h651 | h651
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h652 | h652
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h653 | h653
                                  · linarith only [h200, h638, h653, hc02, hlam, hphi, ht23, ht34, u4elo2]
                                  · linarith only [h0, h200, h653, hc12, hlam, hphi, ht23, ht34, u4elo4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h656 | h656
                                  · linarith only [h0, h200, h638, h656, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                  · linarith only [h0, h200, h656, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h1, h646, h651, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h544, h545, h638, h646, hc13, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h661 | h661
              · rcases m.htr 0 4 5 (by decide) (by decide) with h662 | h662
                · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
                  · linarith only [h0, h4, h663, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h665 | h665
                    · linarith only [h0, h200, h665, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h667 | h667
                      · linarith only [h0, h459, h667, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h669 | h669
                        · linarith only [h1, h544, h669, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h671 | h671
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h672 | h672
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h673 | h673
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h674 | h674
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h675 | h675
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h676 | h676
                                    · rcases h0bigk with h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [hlam, p677_0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        rcases p677_3 (m.d 0 1) (by simp) with h679 | h679
                                        · rcases p677_3 (m.d 0 2) (by simp) with h680 | h680
                                          · linarith only [h0, h680, hlam]
                                          · rcases p677_3 (m.d 0 3) (by simp) with h682 | h682
                                            · linarith only [h1, h682, hlam]
                                            · linarith only [h4, h682, hlam]
                                        · linarith only [h0, h679, hlam]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h1, h671, hc35, hlam, hphi, ht0b, ht5b, p677_1, u0elo0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h1, h544, h671, h676, hc45, hlam, hphi, ht0b, ht5b, p677_1, u0elo0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        rcases p677_3 (m.d 0 1) (by simp) with h688 | h688
                                        · rcases p677_3 (m.d 0 2) (by simp) with h689 | h689
                                          · linarith only [h0, h689, hlam]
                                          · rcases p677_3 (m.d 0 3) (by simp) with h691 | h691
                                            · linarith only [h1, h691, hlam]
                                            · linarith only [h661, h691, hlam]
                                        · linarith only [h3, h688, hlam]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h0, hlam, p677_0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [hlam, p677_0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h4, hlam, p677_0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h200, hlam, p677_1]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h459, hlam, p677_0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h1, hlam, p677_1]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h0, h544, h673, hc12, hlam, hphi, ht23, ht34, p677_1, u4elo2]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [hlam, p677_0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h544, hlam, p677_1]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h544, h673, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p677_1, u4elo2]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h2, hlam, p677_0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, p677_1, u4elo0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h544, h673, hc03, hlam, hphi, ht34, p677_1, u4elo2]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [hlam, p677_0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h0, h459, h544, h673, hc12, hlam, hphi, ht23, ht34, p677_1, u4elo2]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h3, hlam, p677_0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h0, h544, h661, h673, hc12, hlam, hphi, ht23, ht34, p677_1, u4elo2]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h661, hlam, p677_0]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [h662, hlam, p677_1]
                                      · have p677_0 := h677c.1
                                        have p677_1 := h677c.2.1
                                        have p677_2 := h677c.2.2.1
                                        have p677_3 := h677c.2.2.2
                                        linarith only [hlam, p677_0]
                                    · linarith only [h544, h676, hc03, hlam, hphi, ht34, u4elo4]
                                  · linarith only [h2, h672, h675, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h1, h544, h671, h673, h674, hlam]
                              · linarith only [h0, h4, h673, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h200, h662, h672, hc14, hlam, hphi, u4elo2]
                          · linarith only [h544, h661, h671, hc13, hlam, hphi, ht34, u4elo3]
                · linarith only [h544, h661, h662, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h722 | h722
                · rcases m.htr 1 2 3 (by decide) (by decide) with h723 | h723
                  · linarith only [h0, h4, h723, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h725 | h725
                    · linarith only [h0, h200, h722, h725, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h727 | h727
                      · linarith only [h1, h459, h544, h723, h727, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h729 | h729
                        · linarith only [h1, h544, h729, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h731 | h731
                          · linarith only [h661, h729, h731, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h733 | h733
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h734 | h734
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h735 | h735
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h736 | h736
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h737 | h737
                                    · rcases h0bigk with h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        rcases p738_3 (m.d 0 1) (by simp) with h740 | h740
                                        · rcases p738_3 (m.d 0 2) (by simp) with h741 | h741
                                          · linarith only [h0, h741, hlam]
                                          · rcases p738_3 (m.d 0 3) (by simp) with h743 | h743
                                            · linarith only [h1, h743, hlam]
                                            · linarith only [h4, h743, hlam]
                                        · linarith only [h0, h740, hlam]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        rcases p738_3 (m.d 0 1) (by simp) with h747 | h747
                                        · rcases p738_3 (m.d 0 2) (by simp) with h748 | h748
                                          · linarith only [h0, h748, hlam]
                                          · rcases p738_3 (m.d 0 3) (by simp) with h750 | h750
                                            · linarith only [h1, h750, hlam]
                                            · rcases p738_3 (m.d 0 4) (by simp) with h752 | h752
                                              · linarith only [h2, h752, hlam]
                                              · linarith only [h544, h752, hlam]
                                        · linarith only [h1, h747, hlam]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h2, h733, hc45, hlam, hphi, ht0b, ht5b, p738_1, u0elo0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        rcases p738_3 (m.d 0 1) (by simp) with h757 | h757
                                        · rcases p738_3 (m.d 0 2) (by simp) with h758 | h758
                                          · linarith only [h0, h758, hlam]
                                          · rcases p738_3 (m.d 0 3) (by simp) with h760 | h760
                                            · linarith only [h1, h760, hlam]
                                            · rcases p738_3 (m.d 0 4) (by simp) with h762 | h762
                                              · linarith only [h2, h762, hlam]
                                              · linarith only [h722, h762, hlam]
                                        · linarith only [h3, h757, hlam]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h0, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h4, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h200, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h459, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h1, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h0, h661, h734, h737, hc12, hc23, hlam, hphi, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h544, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h661, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h2, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, p738_1, u4elo0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h200, hc03, hlam, hphi, ht34, p738_1, u4elo2]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h0, h200, h4, h661, hc12, hlam, hphi, ht23, ht34, p738_1, u4elo2]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h3, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h0, h459, h736, hc12, hlam, hphi, ht23, ht34, p738_1, u4elo2]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h0, h4, h661, h735, h736, hc12, hlam, hphi, ht23, ht34, p738_1, u4elo2]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h722, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                    · linarith only [h544, h733, h737, hc04, hlam, hphi, u4elo1]
                                  · linarith only [h2, h544, h733, h734, h736, hlam]
                                · linarith only [h0, h4, h544, h734, h735, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h4, h734, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h200, h722, h733, hc14, hlam, hphi, u4elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h791 | h791
                  · linarith only [h0, h4, h791, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h793 | h793
                    · linarith only [h0, h200, h793, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h795 | h795
                      · linarith only [h0, h459, h795, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h797 | h797
                        · linarith only [h1, h544, h722, h797, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h799 | h799
                          · linarith only [h1, h661, h799, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h801 | h801
                            · linarith only [h2, h544, h722, h801, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h803 | h803
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h804 | h804
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h805 | h805
                                  · linarith only [h0, h4, h544, h722, h805, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                  · linarith only [h0, h200, h805, hc12, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h0, h4, h544, h803, h804, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h4, h803, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h810 | h810
      · rcases m.htr 0 2 4 (by decide) (by decide) with h811 | h811
        · rcases m.htr 0 2 5 (by decide) (by decide) with h812 | h812
          · linarith only [h0, h3, h812, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h814 | h814
            · rcases m.htr 0 3 5 (by decide) (by decide) with h815 | h815
              · linarith only [h1, h3, h815, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h817 | h817
                · linarith only [h2, h3, h817, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h819 | h819
                  · linarith only [h0, h3, h817, h819, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h3, h810, h817, h819, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h822 | h822
              · linarith only [h1, h3, h822, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h824 | h824
                · linarith only [h2, h3, h824, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h826 | h826
                  · linarith only [h0, h3, h824, h826, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h3, h810, h824, h826, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · linarith only [h810, h811, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h830 | h830
        · rcases m.htr 0 2 5 (by decide) (by decide) with h831 | h831
          · linarith only [h0, h3, h831, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h833 | h833
            · rcases m.htr 0 3 5 (by decide) (by decide) with h834 | h834
              · linarith only [h1, h3, h834, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h836 | h836
                · linarith only [h2, h3, h836, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h838 | h838
                  · linarith only [h0, h810, h838, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h840 | h840
                    · linarith only [h0, h3, h836, h840, hc24, hlam, hphi, u4elo4]
                    · linarith only [h810, h830, h840, hc12, hc23, hlam, hphi]
            · linarith only [h810, h830, h833, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h844 | h844
          · linarith only [h0, h3, h830, h844, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h846 | h846
            · rcases m.htr 0 3 5 (by decide) (by decide) with h847 | h847
              · linarith only [h1, h3, h847, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h849 | h849
                · linarith only [h2, h3, h849, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h851 | h851
                  · linarith only [h0, h810, h851, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h853 | h853
                    · linarith only [h0, h3, h849, h853, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h855 | h855
                      · linarith only [h1, h3, h844, h851, h855, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h857 | h857
                        · linarith only [h1, h3, h849, h857, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1, h3, h846, h849, h851, h857, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h860 | h860
              · linarith only [h2, h3, h846, h860, hc14, hlam, hphi, u4elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h862 | h862
                · linarith only [h2, h3, h862, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h864 | h864
                  · linarith only [h0, h810, h864, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h866 | h866
                    · linarith only [h0, h830, h866, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h868 | h868
                      · linarith only [h0, h844, h868, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h870 | h870
                        · linarith only [h1, h846, h862, h870, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h872 | h872
                          · linarith only [h0, h3, h860, h870, h872, hc12, hlam, hphi, ht23, ht34, u4elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h874 | h874
                            · linarith only [h2, h846, h862, h874, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h0, h3, h874, hc12, hlam, hphi, ht23, ht34, u4elo4]
  · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]

end R2N4
