import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S78
import Jsp000404.R1LeavesN7_0S79
import Jsp000404.R1LeavesN7_0S80
import Jsp000404.R1LeavesN7_0S81

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13704000 in
set_option maxHeartbeats 13704000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h41027 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h45992 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h46639 | h46639
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 h41027 h45992 h46639
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 h41027 h45992 h46639

set_option maxHeartbeats 13704000 in
set_option maxHeartbeats 13704000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h41027 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h45992 | h45992
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 h41027 h45992
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 h41027 h45992

set_option maxHeartbeats 13704000 in
set_option maxHeartbeats 13704000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h41027 | h41027
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 h41027
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 h41027

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h39236 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h39237 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h39238 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h39239 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h39240 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h39241 | h39241
  · rcases m.htr 2 4 5 (by decide) (by decide) with h39242 | h39242
    · rcases m.htr 3 4 5 (by decide) (by decide) with h39243 | h39243
      · rcases h1bigk with h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c | h39244c
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h0, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h33187, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h36828, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          rcases p39244_3 (m.d 0 1) (by simp) with h39249 | h39249
          · rcases p39244_3 (m.d 1 2) (by simp) with h39250 | h39250
            · rcases p39244_3 (m.d 1 3) (by simp) with h39251 | h39251
              · rcases p39244_3 (m.d 1 4) (by simp) with h39252 | h39252
                · rcases p39244_3 (m.d 1 5) (by simp) with h39253 | h39253
                  · linarith only [h39253, hlam, p39244_0]
                  · rcases h1emax with h39255 | h39255 | h39255 | h39255 | h39255
                    · linarith only [h39236, h39241, h39243, h39255, hc45, hlam, hphi, ht01, ht0b, ht5b, p39244_1]
                    · linarith only [h36828, h39234, h39236, h39237, h39241, h39243, h39255, hc45, hlam, hphi, ht01, ht0b, ht5b, p39244_1]
                    · linarith only [h36828, h39236, h39237, h39241, h39243, h39255, hc45, hlam, hphi, ht01, ht0b, ht5b, p39244_1]
                    · linarith only [h36828, h39236, h39241, h39243, h39255, hc45, hlam, hphi, ht01, ht0b, ht5b, p39244_1]
                    · rcases h2bigk with h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c | h39260c
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h0, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h0, h39240, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39260_1]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        rcases p39260_3 (m.d 0 2) (by simp) with h39264 | h39264
                        · rcases p39260_3 (m.d 1 2) (by simp) with h39265 | h39265
                          · rcases p39260_3 (m.d 2 3) (by simp) with h39266 | h39266
                            · linarith only [h39228, h39266, hlam]
                            · linarith only [h39240, h39266, hlam]
                          · linarith only [h39235, h39265, hlam]
                        · linarith only [h39264, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        rcases p39260_3 (m.d 0 2) (by simp) with h39271 | h39271
                        · rcases p39260_3 (m.d 1 2) (by simp) with h39272 | h39272
                          · rcases p39260_3 (m.d 2 3) (by simp) with h39273 | h39273
                            · linarith only [h39228, h39273, hlam]
                            · linarith only [h39241, h39273, hlam]
                          · linarith only [h39236, h39272, hlam]
                        · linarith only [h39271, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h0, h39236, h39241, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39244_1, p39260_1]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39240, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39260_1]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        rcases p39260_3 (m.d 0 2) (by simp) with h39281 | h39281
                        · linarith only [h0, h39281, hlam]
                        · linarith only [h39229, h39281, hlam]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h36828, h39234, h39236, h39237, hlam, p39244_1, p39260_2]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39228, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39234, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39228, h39240, h39243, hc02, hc45, hlam, hphi, ht0b, ht5b, p39260_1]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        rcases p39260_3 (m.d 0 2) (by simp) with h39289 | h39289
                        · rcases p39260_3 (m.d 1 2) (by simp) with h39290 | h39290
                          · rcases p39260_3 (m.d 2 3) (by simp) with h39291 | h39291
                            · rcases p39260_3 (m.d 2 4) (by simp) with h39292 | h39292
                              · linarith only [h39240, h39292, hlam]
                              · linarith only [h39242, h39292, hlam]
                            · linarith only [h39241, h39291, hlam]
                          · linarith only [h39236, h39290, hlam]
                        · linarith only [h39230, h39289, hlam]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39229, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39235, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39240, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        rcases p39260_3 (m.d 0 2) (by simp) with h39302 | h39302
                        · rcases p39260_3 (m.d 1 2) (by simp) with h39303 | h39303
                          · rcases p39260_3 (m.d 2 3) (by simp) with h39304 | h39304
                            · rcases p39260_3 (m.d 2 4) (by simp) with h39305 | h39305
                              · rcases p39260_3 (m.d 2 5) (by simp) with h39306 | h39306
                                · linarith only [h39242, h39306, hlam]
                                · rcases h4bigk with h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c | h39308c
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h36828, hlam, p39308_1]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39231, h39241, h39243, hc03, hc45, hlam, hphi, ht0b, ht5b, p39260_1, p39308_1]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    rcases p39308_3 (m.d 0 4) (by simp) with h39312 | h39312
                                    · rcases p39308_3 (m.d 1 4) (by simp) with h39313 | h39313
                                      · rcases p39308_3 (m.d 2 4) (by simp) with h39314 | h39314
                                        · linarith only [h39229, h39314, hlam]
                                        · linarith only [h39240, h39314, hlam]
                                      · linarith only [h39237, h39313, hlam]
                                    · linarith only [h39231, h39312, hlam]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    rcases p39308_3 (m.d 0 4) (by simp) with h39319 | h39319
                                    · rcases p39308_3 (m.d 1 4) (by simp) with h39320 | h39320
                                      · rcases p39308_3 (m.d 2 4) (by simp) with h39321 | h39321
                                        · linarith only [h39229, h39321, hlam]
                                        · linarith only [h39242, h39321, hlam]
                                      · linarith only [h39239, h39320, hlam]
                                    · linarith only [h39319, hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h36828, h39236, h39241, h39243, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p39244_1, p39308_1]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39235, h39241, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39260_1, p39308_1]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    rcases p39308_3 (m.d 0 4) (by simp) with h39329 | h39329
                                    · linarith only [h36828, h39329, hlam]
                                    · linarith only [h39231, h39329, hlam]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h36828, h39236, h39241, h39243, hlam, p39244_1, p39308_2]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39229, hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39235, hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h0, h39229, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39308_1]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    rcases p39308_3 (m.d 0 4) (by simp) with h39337 | h39337
                                    · rcases p39308_3 (m.d 1 4) (by simp) with h39338 | h39338
                                      · rcases p39308_3 (m.d 2 4) (by simp) with h39339 | h39339
                                        · rcases p39308_3 (m.d 3 4) (by simp) with h39340 | h39340
                                          · linarith only [h39240, h39340, hlam]
                                          · linarith only [h39243, h39340, hlam]
                                        · linarith only [h39339, hlam, p39308_0]
                                      · linarith only [h39239, h39338, hlam]
                                    · linarith only [h39233, h39337, hlam]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39231, hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39237, hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39240, hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h0, h39228, h39240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39308_1]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39233, hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39239, hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39242, hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [h39243, hlam, p39308_0]
                                  · have p39308_0 := h39308c.1
                                    have p39308_1 := h39308c.2.1
                                    have p39308_2 := h39308c.2.2.1
                                    have p39308_3 := h39308c.2.2.2
                                    linarith only [hlam, p39308_0]
                              · linarith only [h39242, h39305, hlam]
                            · linarith only [h39241, h39304, hlam]
                          · linarith only [h39236, h39303, hlam]
                        · linarith only [h39230, h39302, hlam]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39230, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39236, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39241, hlam, p39260_0]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [h39242, hlam, p39260_1]
                      · have p39260_0 := h39260c.1
                        have p39260_1 := h39260c.2.1
                        have p39260_2 := h39260c.2.2.1
                        have p39260_3 := h39260c.2.2.2
                        linarith only [hlam, p39260_0]
                · linarith only [h39239, h39252, hlam]
              · linarith only [h39238, h39251, hlam]
            · linarith only [h39236, h39250, hlam]
          · linarith only [h39249, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          rcases p39244_3 (m.d 0 1) (by simp) with h39369 | h39369
          · linarith only [h39369, hlam, p39244_0]
          · rcases p39244_3 (m.d 1 2) (by simp) with h39371 | h39371
            · rcases p39244_3 (m.d 1 3) (by simp) with h39372 | h39372
              · linarith only [h39234, h39372, hlam]
              · linarith only [h33187, h39372, hlam]
            · linarith only [h39371, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h33187, hc01, hc12, hlam, hphi, p39244_1]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h36828, h39227, h39236, h39241, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39244_1]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          rcases p39244_3 (m.d 0 1) (by simp) with h39379 | h39379
          · linarith only [h0, h39379, hlam]
          · linarith only [h39227, h39379, hlam]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          rcases p39244_3 (m.d 0 1) (by simp) with h39382 | h39382
          · linarith only [h39382, hlam, p39244_0]
          · rcases p39244_3 (m.d 1 2) (by simp) with h39384 | h39384
            · rcases p39244_3 (m.d 1 3) (by simp) with h39385 | h39385
              · rcases p39244_3 (m.d 1 4) (by simp) with h39386 | h39386
                · linarith only [h39237, h39386, hlam]
                · linarith only [h36828, h39386, hlam]
              · linarith only [h39385, hlam, p39244_0]
            · linarith only [h0, h39384, hlam]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h39234, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h36828, h39227, h39234, h39236, h39241, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39244_1]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          rcases p39244_3 (m.d 0 1) (by simp) with h39394 | h39394
          · linarith only [h33187, h39394, hlam]
          · linarith only [h39227, h39394, hlam]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          rcases p39244_3 (m.d 0 1) (by simp) with h39397 | h39397
          · linarith only [h39397, hlam, p39244_0]
          · rcases p39244_3 (m.d 1 2) (by simp) with h39399 | h39399
            · rcases p39244_3 (m.d 1 3) (by simp) with h39400 | h39400
              · rcases p39244_3 (m.d 1 4) (by simp) with h39401 | h39401
                · rcases p39244_3 (m.d 1 5) (by simp) with h39402 | h39402
                  · linarith only [h39239, h39402, hlam]
                  · rcases h1emax with h39404 | h39404 | h39404 | h39404 | h39404
                    · rcases h2bigk with h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c | h39405c
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h0, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h0, h39240, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39405_1]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        rcases p39405_3 (m.d 0 2) (by simp) with h39409 | h39409
                        · rcases p39405_3 (m.d 1 2) (by simp) with h39410 | h39410
                          · rcases p39405_3 (m.d 2 3) (by simp) with h39411 | h39411
                            · linarith only [h39228, h39411, hlam]
                            · linarith only [h39240, h39411, hlam]
                          · linarith only [h39235, h39410, hlam]
                        · linarith only [h39409, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        rcases p39405_3 (m.d 0 2) (by simp) with h39416 | h39416
                        · rcases p39405_3 (m.d 1 2) (by simp) with h39417 | h39417
                          · rcases p39405_3 (m.d 2 3) (by simp) with h39418 | h39418
                            · linarith only [h39228, h39418, hlam]
                            · linarith only [h39241, h39418, hlam]
                          · linarith only [h39236, h39417, hlam]
                        · linarith only [h39416, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39228, h39240, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39405_1]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39240, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39405_1]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        rcases p39405_3 (m.d 0 2) (by simp) with h39426 | h39426
                        · linarith only [h0, h39426, hlam]
                        · linarith only [h39229, h39426, hlam]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39227, h39234, h39236, h39237, hlam, p39244_1, p39405_2]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39228, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39234, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39228, h39240, h39243, hc02, hc45, hlam, hphi, ht0b, ht5b, p39405_1]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        rcases p39405_3 (m.d 0 2) (by simp) with h39434 | h39434
                        · rcases p39405_3 (m.d 1 2) (by simp) with h39435 | h39435
                          · rcases p39405_3 (m.d 2 3) (by simp) with h39436 | h39436
                            · rcases p39405_3 (m.d 2 4) (by simp) with h39437 | h39437
                              · linarith only [h39240, h39437, hlam]
                              · linarith only [h39242, h39437, hlam]
                            · linarith only [h39241, h39436, hlam]
                          · linarith only [h39236, h39435, hlam]
                        · linarith only [h39230, h39434, hlam]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39229, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39235, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39240, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        rcases p39405_3 (m.d 0 2) (by simp) with h39447 | h39447
                        · rcases p39405_3 (m.d 1 2) (by simp) with h39448 | h39448
                          · rcases p39405_3 (m.d 2 3) (by simp) with h39449 | h39449
                            · rcases p39405_3 (m.d 2 4) (by simp) with h39450 | h39450
                              · rcases p39405_3 (m.d 2 5) (by simp) with h39451 | h39451
                                · linarith only [h39242, h39451, hlam]
                                · rcases h4bigk with h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c | h39453c
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h36828, hlam, p39453_1]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h0, h39228, h39231, h39241, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39405_1, p39453_1]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    rcases p39453_3 (m.d 0 4) (by simp) with h39457 | h39457
                                    · rcases p39453_3 (m.d 1 4) (by simp) with h39458 | h39458
                                      · rcases p39453_3 (m.d 2 4) (by simp) with h39459 | h39459
                                        · linarith only [h39229, h39459, hlam]
                                        · linarith only [h39240, h39459, hlam]
                                      · linarith only [h39237, h39458, hlam]
                                    · linarith only [h39231, h39457, hlam]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    rcases p39453_3 (m.d 0 4) (by simp) with h39464 | h39464
                                    · rcases p39453_3 (m.d 1 4) (by simp) with h39465 | h39465
                                      · rcases p39453_3 (m.d 2 4) (by simp) with h39466 | h39466
                                        · linarith only [h39229, h39466, hlam]
                                        · linarith only [h39242, h39466, hlam]
                                      · linarith only [h39239, h39465, hlam]
                                    · linarith only [h39464, hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39229, h39241, h39243, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p39405_1, p39453_1]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39235, h39241, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39405_1, p39453_1]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    rcases p39453_3 (m.d 0 4) (by simp) with h39474 | h39474
                                    · linarith only [h36828, h39474, hlam]
                                    · linarith only [h39231, h39474, hlam]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39227, h39236, h39241, h39243, hlam, p39244_1, p39453_2]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39229, hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39235, hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h0, h39229, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39453_1]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    rcases p39453_3 (m.d 0 4) (by simp) with h39482 | h39482
                                    · rcases p39453_3 (m.d 1 4) (by simp) with h39483 | h39483
                                      · rcases p39453_3 (m.d 2 4) (by simp) with h39484 | h39484
                                        · rcases p39453_3 (m.d 3 4) (by simp) with h39485 | h39485
                                          · linarith only [h39240, h39485, hlam]
                                          · linarith only [h39243, h39485, hlam]
                                        · linarith only [h39484, hlam, p39453_0]
                                      · linarith only [h39239, h39483, hlam]
                                    · linarith only [h39233, h39482, hlam]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39231, hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39237, hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39240, hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h0, h39228, h39240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39453_1]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39233, hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39239, hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39242, hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [h39243, hlam, p39453_0]
                                  · have p39453_0 := h39453c.1
                                    have p39453_1 := h39453c.2.1
                                    have p39453_2 := h39453c.2.2.1
                                    have p39453_3 := h39453c.2.2.2
                                    linarith only [hlam, p39453_0]
                              · linarith only [h39242, h39450, hlam]
                            · linarith only [h39241, h39449, hlam]
                          · linarith only [h39236, h39448, hlam]
                        · linarith only [h39230, h39447, hlam]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39230, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39236, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39241, hlam, p39405_0]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [h39242, hlam, p39405_1]
                      · have p39405_0 := h39405c.1
                        have p39405_1 := h39405c.2.1
                        have p39405_2 := h39405c.2.2.1
                        have p39405_3 := h39405c.2.2.2
                        linarith only [hlam, p39405_0]
                    · linarith only [h0, h39228, h39240, h39404, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h39227, h39236, h39237, h39241, h39243, h39404, hc45, hlam, hphi, ht01, ht0b, ht5b, p39244_1]
                    · linarith only [h39227, h39236, h39241, h39243, h39404, hc45, hlam, hphi, ht01, ht0b, ht5b, p39244_1]
                    · rcases h2bigk with h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c | h39513c
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h0, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39240, h39243, hc02, hc45, hlam, hphi, ht0b, ht5b, p39513_1]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        rcases p39513_3 (m.d 0 2) (by simp) with h39517 | h39517
                        · rcases p39513_3 (m.d 1 2) (by simp) with h39518 | h39518
                          · rcases p39513_3 (m.d 2 3) (by simp) with h39519 | h39519
                            · linarith only [h39228, h39519, hlam]
                            · linarith only [h39240, h39519, hlam]
                          · linarith only [h39235, h39518, hlam]
                        · linarith only [h39517, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        rcases p39513_3 (m.d 0 2) (by simp) with h39524 | h39524
                        · rcases p39513_3 (m.d 1 2) (by simp) with h39525 | h39525
                          · rcases p39513_3 (m.d 2 3) (by simp) with h39526 | h39526
                            · linarith only [h39228, h39526, hlam]
                            · linarith only [h39241, h39526, hlam]
                          · linarith only [h39236, h39525, hlam]
                        · linarith only [h39524, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39228, h39240, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39513_1]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39240, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39513_1]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        rcases p39513_3 (m.d 0 2) (by simp) with h39534 | h39534
                        · linarith only [h0, h39534, hlam]
                        · linarith only [h39229, h39534, hlam]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39227, h39234, h39236, h39237, hlam, p39244_1, p39513_2]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39228, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39234, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39228, h39240, h39243, hc02, hc45, hlam, hphi, ht0b, ht5b, p39513_1]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        rcases p39513_3 (m.d 0 2) (by simp) with h39542 | h39542
                        · rcases p39513_3 (m.d 1 2) (by simp) with h39543 | h39543
                          · rcases p39513_3 (m.d 2 3) (by simp) with h39544 | h39544
                            · rcases p39513_3 (m.d 2 4) (by simp) with h39545 | h39545
                              · linarith only [h39240, h39545, hlam]
                              · linarith only [h39242, h39545, hlam]
                            · linarith only [h39241, h39544, hlam]
                          · linarith only [h39236, h39543, hlam]
                        · linarith only [h39230, h39542, hlam]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39229, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39235, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39240, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        rcases p39513_3 (m.d 0 2) (by simp) with h39555 | h39555
                        · rcases p39513_3 (m.d 1 2) (by simp) with h39556 | h39556
                          · rcases p39513_3 (m.d 2 3) (by simp) with h39557 | h39557
                            · rcases p39513_3 (m.d 2 4) (by simp) with h39558 | h39558
                              · rcases p39513_3 (m.d 2 5) (by simp) with h39559 | h39559
                                · linarith only [h39242, h39559, hlam]
                                · rcases h4bigk with h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c | h39561c
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h36828, hlam, p39561_1]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39241, h39243, hc04, hc45, hlam, hphi, ht0b, ht5b, p39513_1, p39561_1]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    rcases p39561_3 (m.d 0 4) (by simp) with h39565 | h39565
                                    · rcases p39561_3 (m.d 1 4) (by simp) with h39566 | h39566
                                      · rcases p39561_3 (m.d 2 4) (by simp) with h39567 | h39567
                                        · linarith only [h39229, h39567, hlam]
                                        · linarith only [h39240, h39567, hlam]
                                      · linarith only [h39237, h39566, hlam]
                                    · linarith only [h39231, h39565, hlam]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    rcases p39561_3 (m.d 0 4) (by simp) with h39572 | h39572
                                    · rcases p39561_3 (m.d 1 4) (by simp) with h39573 | h39573
                                      · rcases p39561_3 (m.d 2 4) (by simp) with h39574 | h39574
                                        · linarith only [h39229, h39574, hlam]
                                        · linarith only [h39242, h39574, hlam]
                                      · linarith only [h39239, h39573, hlam]
                                    · linarith only [h39572, hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39229, h39234, h39237, h39241, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39513_1, p39561_1]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39234, h39237, h39241, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39513_1, p39561_1]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    rcases p39561_3 (m.d 0 4) (by simp) with h39582 | h39582
                                    · linarith only [h36828, h39582, hlam]
                                    · linarith only [h39231, h39582, hlam]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39227, h39236, h39241, h39243, hlam, p39244_1, p39561_2]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39229, hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39235, hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h0, h39229, h39243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39561_1]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    rcases p39561_3 (m.d 0 4) (by simp) with h39590 | h39590
                                    · rcases p39561_3 (m.d 1 4) (by simp) with h39591 | h39591
                                      · rcases p39561_3 (m.d 2 4) (by simp) with h39592 | h39592
                                        · rcases p39561_3 (m.d 3 4) (by simp) with h39593 | h39593
                                          · linarith only [h39240, h39593, hlam]
                                          · linarith only [h39243, h39593, hlam]
                                        · linarith only [h39592, hlam, p39561_0]
                                      · linarith only [h39239, h39591, hlam]
                                    · linarith only [h39233, h39590, hlam]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39231, hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39237, hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39240, hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h0, h39228, h39240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39561_1]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39233, hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39239, hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39242, hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [h39243, hlam, p39561_0]
                                  · have p39561_0 := h39561c.1
                                    have p39561_1 := h39561c.2.1
                                    have p39561_2 := h39561c.2.2.1
                                    have p39561_3 := h39561c.2.2.2
                                    linarith only [hlam, p39561_0]
                              · linarith only [h39242, h39558, hlam]
                            · linarith only [h39241, h39557, hlam]
                          · linarith only [h39236, h39556, hlam]
                        · linarith only [h39230, h39555, hlam]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39230, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39236, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39241, hlam, p39513_0]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [h39242, hlam, p39513_1]
                      · have p39513_0 := h39513c.1
                        have p39513_1 := h39513c.2.1
                        have p39513_2 := h39513c.2.2.1
                        have p39513_3 := h39513c.2.2.2
                        linarith only [hlam, p39513_0]
                · linarith only [h39401, hlam, p39244_0]
              · linarith only [h33187, h39400, hlam]
            · linarith only [h0, h39399, hlam]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h39235, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h39237, hlam, p39244_1]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          rcases p39244_3 (m.d 0 1) (by simp) with h39624 | h39624
          · linarith only [h36828, h39624, hlam]
          · linarith only [h39227, h39624, hlam]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h39227, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h39236, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h39238, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [h39239, hlam, p39244_0]
        · have p39244_0 := h39244c.1
          have p39244_1 := h39244c.2.1
          have p39244_2 := h39244c.2.2.1
          have p39244_3 := h39244c.2.2.2
          linarith only [hlam, p39244_0]
      · rcases h1bigk with h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c | h39632c
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h0, hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h33187, hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h36828, hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h36828, h39234, h39236, h39237, h39242, h39243, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39632_1]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h39227, h39236, h39242, h39243, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39632_1]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h33187, hc01, hc12, hlam, hphi, p39632_1]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h36828, h39227, h39236, h39242, h39243, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39632_1]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          rcases p39632_3 (m.d 0 1) (by simp) with h39642 | h39642
          · linarith only [h0, h39642, hlam]
          · linarith only [h39227, h39642, hlam]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h39227, h39236, h39242, h39243, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39632_1]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h39234, hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h36828, h39227, h39234, h39236, h39242, h39243, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39632_1]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          rcases p39632_3 (m.d 0 1) (by simp) with h39649 | h39649
          · linarith only [h33187, h39649, hlam]
          · linarith only [h39227, h39649, hlam]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h39227, h39236, h39242, h39243, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39632_1]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h39235, hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h39237, hlam, p39632_1]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          rcases p39632_3 (m.d 0 1) (by simp) with h39656 | h39656
          · linarith only [h36828, h39656, hlam]
          · linarith only [h39227, h39656, hlam]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h39227, hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h39236, hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h39238, hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [h39239, hlam, p39632_0]
        · have p39632_0 := h39632c.1
          have p39632_1 := h39632c.2.1
          have p39632_2 := h39632c.2.2.1
          have p39632_3 := h39632c.2.2.2
          linarith only [hlam, p39632_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h39664 | h39664
      · linarith only [h0, h39228, h39240, h39242, h39664, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h1bigk with h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c | h39666c
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h0, hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h33187, hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h36828, hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h36828, h39234, h39237, h39239, h39242, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p39666_1]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h39227, h39239, h39240, h39242, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39666_1]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h33187, hc01, hc12, hlam, hphi, p39666_1]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h36828, h39227, h39239, h39240, h39242, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39666_1]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          rcases p39666_3 (m.d 0 1) (by simp) with h39676 | h39676
          · linarith only [h0, h39676, hlam]
          · linarith only [h39227, h39676, hlam]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h39227, h39239, h39240, h39242, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39666_1]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h39234, hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h36828, h39227, h39234, h39239, h39240, h39242, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39666_1]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          rcases p39666_3 (m.d 0 1) (by simp) with h39683 | h39683
          · linarith only [h33187, h39683, hlam]
          · linarith only [h39227, h39683, hlam]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h39227, h39239, h39240, h39242, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39666_1]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h39235, hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h39237, hlam, p39666_1]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          rcases p39666_3 (m.d 0 1) (by simp) with h39690 | h39690
          · linarith only [h36828, h39690, hlam]
          · linarith only [h39227, h39690, hlam]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h39227, hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h39236, hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h39238, hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [h39239, hlam, p39666_0]
        · have p39666_0 := h39666c.1
          have p39666_1 := h39666c.2.1
          have p39666_2 := h39666c.2.2.1
          have p39666_3 := h39666c.2.2.2
          linarith only [hlam, p39666_0]
  · linarith only [h0, h39227, h39238, h39240, h39241, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]

end R2N4
