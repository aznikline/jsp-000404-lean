import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S7
import Jsp000404.R1LeavesN7_23S8
import Jsp000404.R1LeavesN7_23S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h4686 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h4905 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases m.htr 3 4 5 (by decide) (by decide) with h5589 | h5589
  · rcases h2bigk with h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h0, hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h3225, h3228, h3237, h4905, h5589, hlam, p5590_2]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h3225, h3228, h4905, h5589, hlam, p5590_2]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      rcases p5590_3 (m.d 0 2) (by simp) with h5595 | h5595
      · rcases p5590_3 (m.d 1 2) (by simp) with h5596 | h5596
        · rcases p5590_3 (m.d 2 3) (by simp) with h5597 | h5597
          · linarith only [h3225, h5597, hlam]
          · rcases p5590_3 (m.d 2 4) (by simp) with h5599 | h5599
            · linarith only [h3226, h5599, hlam]
            · rcases p5590_3 (m.d 2 5) (by simp) with h5601 | h5601
              · linarith only [h5601, hlam, p5590_0]
              · rcases h2emax with h5603 | h5603 | h5603 | h5603 | h5603
                · linarith only [h3225, h3228, h3237, h4905, h5589, h5603, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h5603, hlam, ht12, u1ehi1]
                · rcases h4bigk with h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c | h5606c
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3221, hlam, p5606_1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 4) (by simp) with h5609 | h5609
                    · rcases p5606_3 (m.d 1 4) (by simp) with h5610 | h5610
                      · rcases p5606_3 (m.d 2 4) (by simp) with h5611 | h5611
                        · linarith only [h3226, h5611, hlam]
                        · rcases p5606_3 (m.d 3 4) (by simp) with h5613 | h5613
                          · linarith only [h3228, h5613, hlam]
                          · linarith only [h3237, h5613, hlam]
                      · linarith only [h3232, h5610, hlam]
                    · linarith only [h3226, h5609, hlam]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3225, h3228, h3237, h4905, h5589, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5606_1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 4) (by simp) with h5619 | h5619
                    · rcases p5606_3 (m.d 1 4) (by simp) with h5620 | h5620
                      · rcases p5606_3 (m.d 2 4) (by simp) with h5621 | h5621
                        · linarith only [h3226, h5621, hlam]
                        · rcases p5606_3 (m.d 3 4) (by simp) with h5623 | h5623
                          · linarith only [h3228, h5623, hlam]
                          · linarith only [h5589, h5623, hlam]
                      · linarith only [h3236, h5620, hlam]
                    · linarith only [h5619, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3221, hc14, hlam, hphi, p5606_1, u1ehi0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 4) (by simp) with h5630 | h5630
                    · linarith only [h3221, h5630, hlam]
                    · linarith only [h3226, h5630, hlam]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3237, h4905, h5589, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5606_1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 4) (by simp) with h5634 | h5634
                    · linarith only [h3221, h5634, hlam]
                    · linarith only [h3230, h5634, hlam]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3226, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3232, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3237, hlam, p5606_1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h4905, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3228, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3234, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    rcases p5606_3 (m.d 0 4) (by simp) with h5644 | h5644
                    · rcases p5606_3 (m.d 1 4) (by simp) with h5645 | h5645
                      · rcases p5606_3 (m.d 2 4) (by simp) with h5646 | h5646
                        · linarith only [h3237, h5646, hlam]
                        · rcases p5606_3 (m.d 3 4) (by simp) with h5648 | h5648
                          · rcases p5606_3 (m.d 4 5) (by simp) with h5649 | h5649
                            · linarith only [h5589, h5649, hlam]
                            · linarith only [h4905, h5649, hlam]
                          · linarith only [h3237, h5648, hlam]
                      · linarith only [h3232, h5645, hlam]
                    · linarith only [h3226, h5644, hlam]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3237, h4905, hc23, hc34, hlam, hphi, p5606_1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3230, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h3236, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h0, h3225, h3228, h3237, h5589, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5606_1]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [h5589, hlam, p5606_0]
                  · have p5606_0 := h5606c.1
                    have p5606_1 := h5606c.2.1
                    have p5606_2 := h5606c.2.2.1
                    have p5606_3 := h5606c.2.2.2
                    linarith only [hlam, p5606_0]
                · rcases h4bigk with h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3221, hlam, p5662_1]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    rcases p5662_3 (m.d 0 4) (by simp) with h5665 | h5665
                    · rcases p5662_3 (m.d 1 4) (by simp) with h5666 | h5666
                      · rcases p5662_3 (m.d 2 4) (by simp) with h5667 | h5667
                        · linarith only [h3226, h5667, hlam]
                        · rcases p5662_3 (m.d 3 4) (by simp) with h5669 | h5669
                          · linarith only [h3228, h5669, hlam]
                          · linarith only [h3237, h5669, hlam]
                      · linarith only [h3232, h5666, hlam]
                    · linarith only [h3226, h5665, hlam]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3226, h4905, h5589, hlam, p5590_2, p5662_1]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    rcases p5662_3 (m.d 0 4) (by simp) with h5675 | h5675
                    · rcases p5662_3 (m.d 1 4) (by simp) with h5676 | h5676
                      · rcases p5662_3 (m.d 2 4) (by simp) with h5677 | h5677
                        · linarith only [h3226, h5677, hlam]
                        · rcases p5662_3 (m.d 3 4) (by simp) with h5679 | h5679
                          · linarith only [h3228, h5679, hlam]
                          · linarith only [h5589, h5679, hlam]
                      · linarith only [h3236, h5676, hlam]
                    · linarith only [h5675, hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p5662_1, u1ehi0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    rcases p5662_3 (m.d 0 4) (by simp) with h5686 | h5686
                    · linarith only [h3221, h5686, hlam]
                    · linarith only [h3226, h5686, hlam]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3237, h4905, h5589, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5662_1]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    rcases p5662_3 (m.d 0 4) (by simp) with h5690 | h5690
                    · linarith only [h3221, h5690, hlam]
                    · linarith only [h3230, h5690, hlam]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3226, hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3232, hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3237, hlam, p5662_1]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h4905, hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3228, hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3234, hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    rcases p5662_3 (m.d 0 4) (by simp) with h5700 | h5700
                    · rcases p5662_3 (m.d 1 4) (by simp) with h5701 | h5701
                      · rcases p5662_3 (m.d 2 4) (by simp) with h5702 | h5702
                        · linarith only [h3237, h5702, hlam]
                        · rcases p5662_3 (m.d 3 4) (by simp) with h5704 | h5704
                          · rcases p5662_3 (m.d 4 5) (by simp) with h5705 | h5705
                            · linarith only [h5589, h5705, hlam]
                            · linarith only [h4905, h5705, hlam]
                          · linarith only [h3237, h5704, hlam]
                      · linarith only [h3232, h5701, hlam]
                    · linarith only [h3226, h5700, hlam]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3225, h3228, h3237, h4905, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5662_1]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3230, hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h3236, hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h0, h3225, h3228, h3237, h5589, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5662_1]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [h5589, hlam, p5662_0]
                  · have p5662_0 := h5662c.1
                    have p5662_1 := h5662c.2.1
                    have p5662_2 := h5662c.2.2.1
                    have p5662_3 := h5662c.2.2.2
                    linarith only [hlam, p5662_0]
                · rcases h4bigk with h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3221, hlam, p5718_1]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    rcases p5718_3 (m.d 0 4) (by simp) with h5721 | h5721
                    · rcases p5718_3 (m.d 1 4) (by simp) with h5722 | h5722
                      · rcases p5718_3 (m.d 2 4) (by simp) with h5723 | h5723
                        · linarith only [h3226, h5723, hlam]
                        · rcases p5718_3 (m.d 3 4) (by simp) with h5725 | h5725
                          · linarith only [h3228, h5725, hlam]
                          · linarith only [h3237, h5725, hlam]
                      · linarith only [h3232, h5722, hlam]
                    · linarith only [h3226, h5721, hlam]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3221, h3231, h3234, h3237, h4905, h5589, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5718_1]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    rcases p5718_3 (m.d 0 4) (by simp) with h5731 | h5731
                    · rcases p5718_3 (m.d 1 4) (by simp) with h5732 | h5732
                      · rcases p5718_3 (m.d 2 4) (by simp) with h5733 | h5733
                        · linarith only [h3226, h5733, hlam]
                        · rcases p5718_3 (m.d 3 4) (by simp) with h5735 | h5735
                          · linarith only [h3228, h5735, hlam]
                          · linarith only [h5589, h5735, hlam]
                      · linarith only [h3236, h5732, hlam]
                    · linarith only [h5731, hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p5718_1, u1ehi0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    rcases p5718_3 (m.d 0 4) (by simp) with h5742 | h5742
                    · linarith only [h3221, h5742, hlam]
                    · linarith only [h3226, h5742, hlam]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3237, h4905, h5589, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5718_1]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    rcases p5718_3 (m.d 0 4) (by simp) with h5746 | h5746
                    · linarith only [h3221, h5746, hlam]
                    · linarith only [h3230, h5746, hlam]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3226, hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3232, hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3237, hlam, p5718_1]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h4905, hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3228, hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3234, hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    rcases p5718_3 (m.d 0 4) (by simp) with h5756 | h5756
                    · rcases p5718_3 (m.d 1 4) (by simp) with h5757 | h5757
                      · rcases p5718_3 (m.d 2 4) (by simp) with h5758 | h5758
                        · linarith only [h3237, h5758, hlam]
                        · rcases p5718_3 (m.d 3 4) (by simp) with h5760 | h5760
                          · rcases p5718_3 (m.d 4 5) (by simp) with h5761 | h5761
                            · linarith only [h5589, h5761, hlam]
                            · linarith only [h4905, h5761, hlam]
                          · linarith only [h3237, h5760, hlam]
                      · linarith only [h3232, h5757, hlam]
                    · linarith only [h3226, h5756, hlam]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3237, h4905, hc23, hc34, hlam, hphi, p5718_1]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3230, hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h3236, hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h0, h3225, h3228, h3237, h5589, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5718_1]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [h5589, hlam, p5718_0]
                  · have p5718_0 := h5718c.1
                    have p5718_1 := h5718c.2.1
                    have p5718_2 := h5718c.2.2.1
                    have p5718_3 := h5718c.2.2.2
                    linarith only [hlam, p5718_0]
        · linarith only [h3233, h5596, hlam]
      · linarith only [h5595, hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h0, hc12, hlam, hphi, p5590_1, u1ehi0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h0, h3225, h3228, h3237, h4905, h5589, hlam, p5590_2]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h0, h3225, h3228, h4905, h5589, hlam, p5590_2]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      rcases p5590_3 (m.d 0 2) (by simp) with h5780 | h5780
      · linarith only [h0, h5780, hlam]
      · linarith only [h3227, h5780, hlam]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h3225, hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h3231, hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h3237, hlam, p5590_1]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h4686, hlam, p5590_1]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h3226, hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h3232, hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h3225, h3228, h4905, h5589, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5590_1]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h4905, hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h3227, hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h3233, hlam, p5590_0]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h0, h3225, h3228, h4905, h5589, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5590_1]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [h0, h3225, h3228, h4905, h5589, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5590_1]
    · have p5590_0 := h5590c.1
      have p5590_1 := h5590c.2.1
      have p5590_2 := h5590c.2.2.1
      have p5590_3 := h5590c.2.2.2
      linarith only [hlam, p5590_0]
  · rcases h2bigk with h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c | h5798c
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h0, hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h3225, h3228, h3230, h3237, h5589, hlam, p5798_2]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      rcases p5798_3 (m.d 0 2) (by simp) with h5802 | h5802
      · rcases p5798_3 (m.d 1 2) (by simp) with h5803 | h5803
        · rcases p5798_3 (m.d 2 3) (by simp) with h5804 | h5804
          · linarith only [h3225, h5804, hlam]
          · rcases p5798_3 (m.d 2 4) (by simp) with h5806 | h5806
            · linarith only [h5806, hlam, p5798_0]
            · rcases p5798_3 (m.d 2 5) (by simp) with h5808 | h5808
              · linarith only [h3227, h5808, hlam]
              · linarith only [h4905, h5808, hlam]
        · linarith only [h3232, h5803, hlam]
      · linarith only [h5802, hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      rcases p5798_3 (m.d 0 2) (by simp) with h5813 | h5813
      · rcases p5798_3 (m.d 1 2) (by simp) with h5814 | h5814
        · rcases p5798_3 (m.d 2 3) (by simp) with h5815 | h5815
          · linarith only [h3225, h5815, hlam]
          · rcases p5798_3 (m.d 2 4) (by simp) with h5817 | h5817
            · linarith only [h3226, h5817, hlam]
            · rcases p5798_3 (m.d 2 5) (by simp) with h5819 | h5819
              · linarith only [h5819, hlam, p5798_0]
              · rcases h2emax with h5821 | h5821 | h5821 | h5821 | h5821
                · linarith only [h3225, h3228, h3230, h3237, h5589, h5821, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h5821, hlam, ht12, u1ehi1]
                · rcases h4bigk with h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c | h5824c
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3221, hlam, p5824_1]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    rcases p5824_3 (m.d 0 4) (by simp) with h5827 | h5827
                    · rcases p5824_3 (m.d 1 4) (by simp) with h5828 | h5828
                      · rcases p5824_3 (m.d 2 4) (by simp) with h5829 | h5829
                        · linarith only [h3226, h5829, hlam]
                        · rcases p5824_3 (m.d 3 4) (by simp) with h5831 | h5831
                          · linarith only [h3228, h5831, hlam]
                          · linarith only [h3237, h5831, hlam]
                      · linarith only [h3232, h5828, hlam]
                    · linarith only [h3226, h5827, hlam]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    rcases p5824_3 (m.d 0 4) (by simp) with h5836 | h5836
                    · rcases p5824_3 (m.d 1 4) (by simp) with h5837 | h5837
                      · rcases p5824_3 (m.d 2 4) (by simp) with h5838 | h5838
                        · linarith only [h3226, h5838, hlam]
                        · rcases p5824_3 (m.d 3 4) (by simp) with h5840 | h5840
                          · linarith only [h3228, h5840, hlam]
                          · rcases p5824_3 (m.d 4 5) (by simp) with h5842 | h5842
                            · linarith only [h3230, h5842, hlam]
                            · linarith only [h5589, h5842, hlam]
                      · linarith only [h3234, h5837, hlam]
                    · linarith only [h3228, h5836, hlam]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3225, h3228, h3237, h5589, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5824_1]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3221, hc14, hlam, hphi, p5824_1, u1ehi0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    rcases p5824_3 (m.d 0 4) (by simp) with h5850 | h5850
                    · linarith only [h3221, h5850, hlam]
                    · linarith only [h3226, h5850, hlam]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    rcases p5824_3 (m.d 0 4) (by simp) with h5853 | h5853
                    · linarith only [h3221, h5853, hlam]
                    · linarith only [h3228, h5853, hlam]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3234, h3237, h5589, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5824_1]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3226, hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3232, hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3237, hlam, p5824_1]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h4905, hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3228, hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3234, hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3230, h5589, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p5824_1]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h5589, hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3230, hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3236, hlam, p5824_0]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    rcases p5824_3 (m.d 0 4) (by simp) with h5869 | h5869
                    · rcases p5824_3 (m.d 1 4) (by simp) with h5870 | h5870
                      · rcases p5824_3 (m.d 2 4) (by simp) with h5871 | h5871
                        · linarith only [h5871, hlam, p5824_0]
                        · rcases p5824_3 (m.d 3 4) (by simp) with h5873 | h5873
                          · linarith only [h5589, h5873, hlam]
                          · linarith only [h3237, h5873, hlam]
                      · linarith only [h3232, h5870, hlam]
                    · linarith only [h3226, h5869, hlam]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [h3221, h3230, h3231, h3234, h3237, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5824_1]
                  · have p5824_0 := h5824c.1
                    have p5824_1 := h5824c.2.1
                    have p5824_2 := h5824c.2.2.1
                    have p5824_3 := h5824c.2.2.2
                    linarith only [hlam, p5824_0]
                · rcases h4bigk with h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3221, hlam, p5880_1]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    rcases p5880_3 (m.d 0 4) (by simp) with h5883 | h5883
                    · rcases p5880_3 (m.d 1 4) (by simp) with h5884 | h5884
                      · rcases p5880_3 (m.d 2 4) (by simp) with h5885 | h5885
                        · linarith only [h3226, h5885, hlam]
                        · rcases p5880_3 (m.d 3 4) (by simp) with h5887 | h5887
                          · linarith only [h3228, h5887, hlam]
                          · linarith only [h3237, h5887, hlam]
                      · linarith only [h3232, h5884, hlam]
                    · linarith only [h3226, h5883, hlam]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    rcases p5880_3 (m.d 0 4) (by simp) with h5892 | h5892
                    · rcases p5880_3 (m.d 1 4) (by simp) with h5893 | h5893
                      · rcases p5880_3 (m.d 2 4) (by simp) with h5894 | h5894
                        · linarith only [h3226, h5894, hlam]
                        · rcases p5880_3 (m.d 3 4) (by simp) with h5896 | h5896
                          · linarith only [h3228, h5896, hlam]
                          · rcases p5880_3 (m.d 4 5) (by simp) with h5898 | h5898
                            · linarith only [h3230, h5898, hlam]
                            · linarith only [h5589, h5898, hlam]
                      · linarith only [h3234, h5893, hlam]
                    · linarith only [h3228, h5892, hlam]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3221, h3231, h3234, h3237, h5589, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5880_1]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p5880_1, u1ehi0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    rcases p5880_3 (m.d 0 4) (by simp) with h5906 | h5906
                    · linarith only [h3221, h5906, hlam]
                    · linarith only [h3226, h5906, hlam]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    rcases p5880_3 (m.d 0 4) (by simp) with h5909 | h5909
                    · linarith only [h3221, h5909, hlam]
                    · linarith only [h3228, h5909, hlam]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3237, h5589, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5880_1]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3226, hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3232, hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3237, hlam, p5880_1]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h4905, hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3228, hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3234, hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3230, h5589, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p5880_1]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h5589, hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3230, hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3236, hlam, p5880_0]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    rcases p5880_3 (m.d 0 4) (by simp) with h5925 | h5925
                    · rcases p5880_3 (m.d 1 4) (by simp) with h5926 | h5926
                      · rcases p5880_3 (m.d 2 4) (by simp) with h5927 | h5927
                        · linarith only [h5927, hlam, p5880_0]
                        · rcases p5880_3 (m.d 3 4) (by simp) with h5929 | h5929
                          · linarith only [h5589, h5929, hlam]
                          · linarith only [h3237, h5929, hlam]
                      · linarith only [h3232, h5926, hlam]
                    · linarith only [h3226, h5925, hlam]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [h3221, h3230, h3231, h3234, h3237, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5880_1]
                  · have p5880_0 := h5880c.1
                    have p5880_1 := h5880c.2.1
                    have p5880_2 := h5880c.2.2.1
                    have p5880_3 := h5880c.2.2.2
                    linarith only [hlam, p5880_0]
                · rcases h4bigk with h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c | h5936c
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3221, hlam, p5936_1]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    rcases p5936_3 (m.d 0 4) (by simp) with h5939 | h5939
                    · rcases p5936_3 (m.d 1 4) (by simp) with h5940 | h5940
                      · rcases p5936_3 (m.d 2 4) (by simp) with h5941 | h5941
                        · linarith only [h3226, h5941, hlam]
                        · rcases p5936_3 (m.d 3 4) (by simp) with h5943 | h5943
                          · linarith only [h3228, h5943, hlam]
                          · linarith only [h3237, h5943, hlam]
                      · linarith only [h3232, h5940, hlam]
                    · linarith only [h3226, h5939, hlam]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    rcases p5936_3 (m.d 0 4) (by simp) with h5948 | h5948
                    · rcases p5936_3 (m.d 1 4) (by simp) with h5949 | h5949
                      · rcases p5936_3 (m.d 2 4) (by simp) with h5950 | h5950
                        · linarith only [h3226, h5950, hlam]
                        · rcases p5936_3 (m.d 3 4) (by simp) with h5952 | h5952
                          · linarith only [h3228, h5952, hlam]
                          · rcases p5936_3 (m.d 4 5) (by simp) with h5954 | h5954
                            · linarith only [h3230, h5954, hlam]
                            · linarith only [h5589, h5954, hlam]
                      · linarith only [h3234, h5949, hlam]
                    · linarith only [h3228, h5948, hlam]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3221, h3231, h3234, h3237, h5589, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5936_1]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p5936_1, u1ehi0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    rcases p5936_3 (m.d 0 4) (by simp) with h5962 | h5962
                    · linarith only [h3221, h5962, hlam]
                    · linarith only [h3226, h5962, hlam]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    rcases p5936_3 (m.d 0 4) (by simp) with h5965 | h5965
                    · linarith only [h3221, h5965, hlam]
                    · linarith only [h3228, h5965, hlam]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3237, h5589, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5936_1]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3226, hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3232, hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3237, hlam, p5936_1]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h4905, hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3228, hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3234, hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3230, h5589, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p5936_1]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h5589, hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3230, hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3236, hlam, p5936_0]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    rcases p5936_3 (m.d 0 4) (by simp) with h5981 | h5981
                    · rcases p5936_3 (m.d 1 4) (by simp) with h5982 | h5982
                      · rcases p5936_3 (m.d 2 4) (by simp) with h5983 | h5983
                        · linarith only [h5983, hlam, p5936_0]
                        · rcases p5936_3 (m.d 3 4) (by simp) with h5985 | h5985
                          · linarith only [h5589, h5985, hlam]
                          · linarith only [h3237, h5985, hlam]
                      · linarith only [h3232, h5982, hlam]
                    · linarith only [h3226, h5981, hlam]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [h3221, h3230, h3231, h3234, h3237, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5936_1]
                  · have p5936_0 := h5936c.1
                    have p5936_1 := h5936c.2.1
                    have p5936_2 := h5936c.2.2.1
                    have p5936_3 := h5936c.2.2.2
                    linarith only [hlam, p5936_0]
        · linarith only [h3233, h5814, hlam]
      · linarith only [h5813, hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h0, hc12, hlam, hphi, p5798_1, u1ehi0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h3221, h3230, h3231, h3234, h3237, h5589, hlam, p5798_2]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      rcases p5798_3 (m.d 0 2) (by simp) with h5997 | h5997
      · linarith only [h0, h5997, hlam]
      · linarith only [h3226, h5997, hlam]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      rcases p5798_3 (m.d 0 2) (by simp) with h6000 | h6000
      · linarith only [h0, h6000, hlam]
      · linarith only [h3227, h6000, hlam]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h3225, hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h3231, hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h3237, hlam, p5798_1]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h4686, hlam, p5798_1]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h3226, hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h3232, hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h3221, h3230, h3231, h3234, h3237, h5589, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5798_1]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h4905, hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h3227, hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [h3233, hlam, p5798_0]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      rcases p5798_3 (m.d 0 2) (by simp) with h6015 | h6015
      · rcases p5798_3 (m.d 1 2) (by simp) with h6016 | h6016
        · rcases p5798_3 (m.d 2 3) (by simp) with h6017 | h6017
          · linarith only [h4686, h6017, hlam]
          · rcases p5798_3 (m.d 2 4) (by simp) with h6019 | h6019
            · linarith only [h4905, h6019, hlam]
            · linarith only [h3237, h6019, hlam]
        · linarith only [h3231, h6016, hlam]
      · linarith only [h3225, h6015, hlam]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      rcases p5798_3 (m.d 0 2) (by simp) with h6024 | h6024
      · rcases p5798_3 (m.d 1 2) (by simp) with h6025 | h6025
        · rcases p5798_3 (m.d 2 3) (by simp) with h6026 | h6026
          · linarith only [h4686, h6026, hlam]
          · rcases p5798_3 (m.d 2 4) (by simp) with h6028 | h6028
            · linarith only [h4905, h6028, hlam]
            · rcases p5798_3 (m.d 2 5) (by simp) with h6030 | h6030
              · rcases h2emax with h6031 | h6031 | h6031 | h6031 | h6031
                · linarith only [h0, h6031, hlam, ht12, u1ehi0]
                · linarith only [h3221, h3230, h3231, h3234, h4686, h5589, h6031, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5798_1]
                · rcases h4bigk with h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c | h6034c
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3221, hlam, p6034_1]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3230, h4686, h5589, hlam, p5798_1, p6034_2]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    rcases p6034_3 (m.d 0 4) (by simp) with h6038 | h6038
                    · rcases p6034_3 (m.d 1 4) (by simp) with h6039 | h6039
                      · rcases p6034_3 (m.d 2 4) (by simp) with h6040 | h6040
                        · linarith only [h3226, h6040, hlam]
                        · rcases p6034_3 (m.d 3 4) (by simp) with h6042 | h6042
                          · linarith only [h3228, h6042, hlam]
                          · rcases p6034_3 (m.d 4 5) (by simp) with h6044 | h6044
                            · linarith only [h3230, h6044, hlam]
                            · linarith only [h5589, h6044, hlam]
                      · linarith only [h3234, h6039, hlam]
                    · linarith only [h3228, h6038, hlam]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3225, h3228, h3237, h4686, h5589, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5798_1, p6034_1]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p6034_1, u1ehi0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3221, h3230, h4686, h5589, hlam, p5798_1, p6034_2]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    rcases p6034_3 (m.d 0 4) (by simp) with h6053 | h6053
                    · linarith only [h3221, h6053, hlam]
                    · linarith only [h3228, h6053, hlam]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3237, h4686, h5589, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5798_1, p6034_1]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3226, hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3232, hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3237, hlam, p6034_1]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h4905, hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3228, hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3234, hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3230, h3237, h5589, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6034_1]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h5589, hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3230, hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3236, hlam, p6034_0]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    rcases p6034_3 (m.d 0 4) (by simp) with h6069 | h6069
                    · rcases p6034_3 (m.d 1 4) (by simp) with h6070 | h6070
                      · rcases p6034_3 (m.d 2 4) (by simp) with h6071 | h6071
                        · linarith only [h6071, hlam, p6034_0]
                        · rcases p6034_3 (m.d 3 4) (by simp) with h6073 | h6073
                          · linarith only [h5589, h6073, hlam]
                          · linarith only [h3237, h6073, hlam]
                      · linarith only [h3232, h6070, hlam]
                    · linarith only [h3226, h6069, hlam]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [h3221, h3230, h3231, h3234, h3237, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6034_1]
                  · have p6034_0 := h6034c.1
                    have p6034_1 := h6034c.2.1
                    have p6034_2 := h6034c.2.2.1
                    have p6034_3 := h6034c.2.2.2
                    linarith only [hlam, p6034_0]
                · rcases h4bigk with h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c | h6080c
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3221, hlam, p6080_1]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3230, h4905, hlam, p5798_1, p6080_2]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    rcases p6080_3 (m.d 0 4) (by simp) with h6084 | h6084
                    · rcases p6080_3 (m.d 1 4) (by simp) with h6085 | h6085
                      · rcases p6080_3 (m.d 2 4) (by simp) with h6086 | h6086
                        · linarith only [h3226, h6086, hlam]
                        · rcases p6080_3 (m.d 3 4) (by simp) with h6088 | h6088
                          · linarith only [h3228, h6088, hlam]
                          · rcases p6080_3 (m.d 4 5) (by simp) with h6090 | h6090
                            · linarith only [h3230, h6090, hlam]
                            · linarith only [h5589, h6090, hlam]
                      · linarith only [h3234, h6085, hlam]
                    · linarith only [h3228, h6084, hlam]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3237, h4686, h5589, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5798_1, p6080_1]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p6080_1, u1ehi0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3221, h3230, h4686, h5589, hlam, p5798_1, p6080_2]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    rcases p6080_3 (m.d 0 4) (by simp) with h6099 | h6099
                    · linarith only [h3221, h6099, hlam]
                    · linarith only [h3228, h6099, hlam]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3237, h4686, h5589, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5798_1, p6080_1]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3226, hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3232, hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3237, hlam, p6080_1]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h4905, hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3228, hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3234, hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3230, h3237, h5589, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6080_1]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h5589, hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3230, hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3236, hlam, p6080_0]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    rcases p6080_3 (m.d 0 4) (by simp) with h6115 | h6115
                    · rcases p6080_3 (m.d 1 4) (by simp) with h6116 | h6116
                      · rcases p6080_3 (m.d 2 4) (by simp) with h6117 | h6117
                        · linarith only [h6117, hlam, p6080_0]
                        · rcases p6080_3 (m.d 3 4) (by simp) with h6119 | h6119
                          · linarith only [h5589, h6119, hlam]
                          · linarith only [h3237, h6119, hlam]
                      · linarith only [h3232, h6116, hlam]
                    · linarith only [h3226, h6115, hlam]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [h3221, h3230, h3231, h3234, h3237, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6080_1]
                  · have p6080_0 := h6080c.1
                    have p6080_1 := h6080c.2.1
                    have p6080_2 := h6080c.2.2.1
                    have p6080_3 := h6080c.2.2.2
                    linarith only [hlam, p6080_0]
                · linarith only [h3237, h6031, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5798_1]
              · linarith only [h4905, h6030, hlam]
        · linarith only [h3232, h6025, hlam]
      · linarith only [h3226, h6024, hlam]
    · have p5798_0 := h5798c.1
      have p5798_1 := h5798c.2.1
      have p5798_2 := h5798c.2.2.1
      have p5798_3 := h5798c.2.2.2
      linarith only [hlam, p5798_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h4686 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases m.htr 2 4 5 (by decide) (by decide) with h4905 | h4905
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h4686 h4905
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h4686 h4905

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases m.htr 2 3 5 (by decide) (by decide) with h4686 | h4686
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h4686
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237 h4686

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases m.htr 2 3 4 (by decide) (by decide) with h3237 | h3237
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x1 m hb1 hb2 hb4 hb5 hg0 hg3219 hg3221 hg3223 hg3225 hg3226 hg3227 hg3228 hg3229 hg3230 hg3231 hg3232 hg3233 hg3234 hg3235 hg3236 h3237

set_option maxHeartbeats 5792000 in
set_option maxHeartbeats 5792000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s18 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  rcases m.htr 1 4 5 (by decide) (by decide) with h3236 | h3236
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226 h3227 h3228 h3229 h3230 h3231 h3232 h3233 h3234 h3235 h3236
  · linarith only [h3221, h3230, h3236, hlam]

set_option maxHeartbeats 5796000 in
set_option maxHeartbeats 5796000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s17 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  rcases m.htr 1 3 5 (by decide) (by decide) with h3235 | h3235
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s18 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226 h3227 h3228 h3229 h3230 h3231 h3232 h3233 h3234 h3235
  · linarith only [h3219, h3235, hc35, hlam, hphi, ht12, ht23, u1ehi0]

set_option maxHeartbeats 5800000 in
set_option maxHeartbeats 5800000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s16 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  rcases m.htr 1 3 4 (by decide) (by decide) with h3234 | h3234
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s17 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226 h3227 h3228 h3229 h3230 h3231 h3232 h3233 h3234
  · linarith only [h3219, h3234, hc34, hlam, hphi, ht12, ht23, u1ehi0]

set_option maxHeartbeats 5804000 in
set_option maxHeartbeats 5804000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s15 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  rcases m.htr 1 2 5 (by decide) (by decide) with h3233 | h3233
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s16 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226 h3227 h3228 h3229 h3230 h3231 h3232 h3233
  · linarith only [h0, h3233, hc25, hlam, hphi, ht12, u1ehi0]

set_option maxHeartbeats 5808000 in
set_option maxHeartbeats 5808000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s14 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  rcases m.htr 1 2 4 (by decide) (by decide) with h3232 | h3232
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s15 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226 h3227 h3228 h3229 h3230 h3231 h3232
  · linarith only [h0, h3232, hc24, hlam, hphi, ht12, u1ehi0]

set_option maxHeartbeats 5812000 in
set_option maxHeartbeats 5812000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s13 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  rcases m.htr 1 2 3 (by decide) (by decide) with h3231 | h3231
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s14 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226 h3227 h3228 h3229 h3230 h3231
  · linarith only [h0, h3231, hc23, hlam, hphi, ht12, u1ehi0]

set_option maxHeartbeats 5840000 in
set_option maxHeartbeats 5840000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s12 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  rcases m.htr 0 4 5 (by decide) (by decide) with h3230 | h3230
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s13 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226 h3227 h3228 h3229 h3230
  · rcases m.htr 1 2 3 (by decide) (by decide) with h6137 | h6137
    · rcases m.htr 1 2 4 (by decide) (by decide) with h6138 | h6138
      · rcases m.htr 1 2 5 (by decide) (by decide) with h6139 | h6139
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6140 | h6140
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6141 | h6141
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6142 | h6142
              · linarith only [h3221, h3230, h6137, h6140, h6142, hc12, hlam, hphi, u1ehi0]
              · linarith only [h3221, h6142, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
            · linarith only [h0, h3225, h3229, h6141, hc12, hlam, hphi, u1ehi2]
          · linarith only [h3219, h6140, hc34, hlam, hphi, ht12, ht23, u1ehi0]
        · linarith only [h0, h3219, h3227, h3229, h6139, hc13, hlam, hphi, u1ehi0]
      · linarith only [h0, h3225, h3226, h3230, h6138, hc23, hc45, hlam, hphi, ht34]
    · linarith only [h0, h6137, hc23, hlam, hphi, ht12, u1ehi0]

set_option maxHeartbeats 5868000 in
set_option maxHeartbeats 5868000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s11 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  rcases m.htr 0 3 5 (by decide) (by decide) with h3229 | h3229
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s12 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226 h3227 h3228 h3229
  · rcases m.htr 0 4 5 (by decide) (by decide) with h6150 | h6150
    · linarith only [h3228, h3229, h6150, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6152 | h6152
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6153 | h6153
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6154 | h6154
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6155 | h6155
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6156 | h6156
              · linarith only [h3219, h3229, h6156, hc13, hlam, hphi, u1ehi0]
              · linarith only [h3219, h6156, hc35, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h3219, h3228, h6155, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
          · linarith only [h0, h6154, hc25, hlam, hphi, ht12, u1ehi0]
        · linarith only [h0, h3226, h6153, hlam]
      · linarith only [h0, h3225, h6152, hlam]

end R2N4
