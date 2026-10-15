import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S42
import Jsp000404.R1LeavesN7_0S43

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x0_x0_x1 (m : N7Model)
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
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h26252 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h26253 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26255 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26256 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26257 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  rcases m.htr 3 4 5 (by decide) (by decide) with h27052 | h27052
  · linarith only [h0, h19744, h26257, h27052, hc12, hc34, hlam, hphi, ht23]
  · rcases h1bigk with h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c | h27054c
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      rcases p27054_3 (m.d 0 1) (by simp) with h27056 | h27056
      · rcases p27054_3 (m.d 1 2) (by simp) with h27057 | h27057
        · linarith only [h27057, hlam, p27054_0]
        · rcases p27054_3 (m.d 1 3) (by simp) with h27059 | h27059
          · linarith only [h1, h27059, hlam]
          · linarith only [h26245, h27059, hlam]
      · linarith only [h27056, hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      rcases p27054_3 (m.d 0 1) (by simp) with h27063 | h27063
      · rcases p27054_3 (m.d 1 2) (by simp) with h27064 | h27064
        · linarith only [h0, h27064, hlam]
        · rcases p27054_3 (m.d 1 3) (by simp) with h27066 | h27066
          · linarith only [h27066, hlam, p27054_0]
          · rcases p27054_3 (m.d 1 4) (by simp) with h27068 | h27068
            · linarith only [h2, h27068, hlam]
            · rcases p27054_3 (m.d 1 5) (by simp) with h27070 | h27070
              · linarith only [h27070, h3, hlam]
              · rcases h1emax with h27072 | h27072 | h27072 | h27072 | h27072
                · linarith only [h27072, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27054_1]
                · rcases h2bigk with h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c | h27074c
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h19744, hc12, hc24, hlam, hphi, p27074_1]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h4, hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h19744, hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h22010, hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h0, hlam, p27074_1]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h26245, hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h26247, hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h26249, hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    rcases p27074_3 (m.d 0 2) (by simp) with h27085 | h27085
                    · linarith only [h27085, hlam, p27074_0]
                    · rcases p27074_3 (m.d 1 2) (by simp) with h27087 | h27087
                      · linarith only [h26245, h27087, hlam]
                      · rcases p27074_3 (m.d 2 3) (by simp) with h27089 | h27089
                        · rcases p27074_3 (m.d 2 4) (by simp) with h27090 | h27090
                          · linarith only [h26255, h27090, hlam]
                          · linarith only [h19744, h27090, hlam]
                        · linarith only [h27089, hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    rcases p27074_3 (m.d 0 2) (by simp) with h27094 | h27094
                    · linarith only [h27094, h4, hlam]
                    · linarith only [h0, h27094, hlam]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h19744, hc02, hc23, hlam, hphi, p27074_1]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27074_1]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h0, h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27074_1]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27074_1]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h26255, hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h26257, hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    rcases p27074_3 (m.d 0 2) (by simp) with h27105 | h27105
                    · linarith only [h27105, hlam, p27074_0]
                    · rcases p27074_3 (m.d 1 2) (by simp) with h27107 | h27107
                      · linarith only [h26249, h27107, hlam]
                      · rcases p27074_3 (m.d 2 3) (by simp) with h27109 | h27109
                        · rcases p27074_3 (m.d 2 4) (by simp) with h27110 | h27110
                          · linarith only [h26257, h27110, hlam]
                          · linarith only [h19744, h27110, hlam]
                        · linarith only [h27109, h4, hlam]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    rcases p27074_3 (m.d 0 2) (by simp) with h27114 | h27114
                    · linarith only [h22010, h27114, hlam]
                    · linarith only [h0, h27114, hlam]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h26256, hlam, p27074_0]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [h0, h19744, hc12, hc25, hlam, hphi, p27074_1]
                  · have p27074_0 := h27074c.1
                    have p27074_1 := h27074c.2.1
                    have p27074_2 := h27074c.2.2.1
                    have p27074_3 := h27074c.2.2.2
                    linarith only [hlam, p27074_0]
                · rcases h2bigk with h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c | h27120c
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h19744, hc12, hc24, hlam, hphi, p27120_1]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h4, hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h19744, hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h22010, hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h0, hlam, p27120_1]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h26245, hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h26247, hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h26249, hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    rcases p27120_3 (m.d 0 2) (by simp) with h27131 | h27131
                    · linarith only [h27131, hlam, p27120_0]
                    · rcases p27120_3 (m.d 1 2) (by simp) with h27133 | h27133
                      · linarith only [h26245, h27133, hlam]
                      · rcases p27120_3 (m.d 2 3) (by simp) with h27135 | h27135
                        · rcases p27120_3 (m.d 2 4) (by simp) with h27136 | h27136
                          · linarith only [h26255, h27136, hlam]
                          · linarith only [h19744, h27136, hlam]
                        · linarith only [h27135, hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    rcases p27120_3 (m.d 0 2) (by simp) with h27140 | h27140
                    · linarith only [h27140, h4, hlam]
                    · linarith only [h0, h27140, hlam]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h19744, hc02, hc23, hlam, hphi, p27120_1]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27120_1]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h0, h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27120_1]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27120_1]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h26255, hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h26257, hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    rcases p27120_3 (m.d 0 2) (by simp) with h27151 | h27151
                    · linarith only [h27151, hlam, p27120_0]
                    · rcases p27120_3 (m.d 1 2) (by simp) with h27153 | h27153
                      · linarith only [h26249, h27153, hlam]
                      · rcases p27120_3 (m.d 2 3) (by simp) with h27155 | h27155
                        · rcases p27120_3 (m.d 2 4) (by simp) with h27156 | h27156
                          · linarith only [h26257, h27156, hlam]
                          · linarith only [h19744, h27156, hlam]
                        · linarith only [h27155, h4, hlam]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    rcases p27120_3 (m.d 0 2) (by simp) with h27160 | h27160
                    · linarith only [h22010, h27160, hlam]
                    · linarith only [h0, h27160, hlam]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h26256, hlam, p27120_0]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [h0, h19744, hc12, hc25, hlam, hphi, p27120_1]
                  · have p27120_0 := h27120c.1
                    have p27120_1 := h27120c.2.1
                    have p27120_2 := h27120c.2.2.1
                    have p27120_3 := h27120c.2.2.2
                    linarith only [hlam, p27120_0]
                · rcases h2bigk with h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c | h27166c
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h19744, hc12, hc24, hlam, hphi, p27166_1]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h4, hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h19744, hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h22010, hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h0, hlam, p27166_1]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h26245, hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h26247, hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h26249, hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    rcases p27166_3 (m.d 0 2) (by simp) with h27177 | h27177
                    · linarith only [h27177, hlam, p27166_0]
                    · rcases p27166_3 (m.d 1 2) (by simp) with h27179 | h27179
                      · linarith only [h26245, h27179, hlam]
                      · rcases p27166_3 (m.d 2 3) (by simp) with h27181 | h27181
                        · rcases p27166_3 (m.d 2 4) (by simp) with h27182 | h27182
                          · linarith only [h26255, h27182, hlam]
                          · linarith only [h19744, h27182, hlam]
                        · linarith only [h27181, hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    rcases p27166_3 (m.d 0 2) (by simp) with h27186 | h27186
                    · linarith only [h27186, h4, hlam]
                    · linarith only [h0, h27186, hlam]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h19744, hc02, hc23, hlam, hphi, p27166_1]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27166_1]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h0, h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27166_1]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27166_1]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h26255, hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h26257, hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    rcases p27166_3 (m.d 0 2) (by simp) with h27197 | h27197
                    · linarith only [h27197, hlam, p27166_0]
                    · rcases p27166_3 (m.d 1 2) (by simp) with h27199 | h27199
                      · linarith only [h26249, h27199, hlam]
                      · rcases p27166_3 (m.d 2 3) (by simp) with h27201 | h27201
                        · rcases p27166_3 (m.d 2 4) (by simp) with h27202 | h27202
                          · linarith only [h26257, h27202, hlam]
                          · linarith only [h19744, h27202, hlam]
                        · linarith only [h27201, h4, hlam]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    rcases p27166_3 (m.d 0 2) (by simp) with h27206 | h27206
                    · linarith only [h22010, h27206, hlam]
                    · linarith only [h0, h27206, hlam]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h26256, hlam, p27166_0]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [h0, h19744, hc12, hc25, hlam, hphi, p27166_1]
                  · have p27166_0 := h27166c.1
                    have p27166_1 := h27166c.2.1
                    have p27166_2 := h27166c.2.2.1
                    have p27166_3 := h27166c.2.2.2
                    linarith only [hlam, p27166_0]
                · rcases h2bigk with h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c | h27212c
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h19744, hc12, hc24, hlam, hphi, p27212_1]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h4, hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h19744, hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h22010, hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h0, hlam, p27212_1]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h26245, hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h26247, hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h26249, hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    rcases p27212_3 (m.d 0 2) (by simp) with h27223 | h27223
                    · linarith only [h27223, hlam, p27212_0]
                    · rcases p27212_3 (m.d 1 2) (by simp) with h27225 | h27225
                      · linarith only [h26245, h27225, hlam]
                      · rcases p27212_3 (m.d 2 3) (by simp) with h27227 | h27227
                        · rcases p27212_3 (m.d 2 4) (by simp) with h27228 | h27228
                          · linarith only [h26255, h27228, hlam]
                          · linarith only [h19744, h27228, hlam]
                        · linarith only [h27227, hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    rcases p27212_3 (m.d 0 2) (by simp) with h27232 | h27232
                    · linarith only [h27232, h4, hlam]
                    · linarith only [h0, h27232, hlam]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h19744, hc02, hc23, hlam, hphi, p27212_1]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27212_1]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h0, h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27212_1]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27212_1]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h26255, hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h26257, hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    rcases p27212_3 (m.d 0 2) (by simp) with h27243 | h27243
                    · linarith only [h27243, hlam, p27212_0]
                    · rcases p27212_3 (m.d 1 2) (by simp) with h27245 | h27245
                      · linarith only [h26249, h27245, hlam]
                      · rcases p27212_3 (m.d 2 3) (by simp) with h27247 | h27247
                        · rcases p27212_3 (m.d 2 4) (by simp) with h27248 | h27248
                          · linarith only [h26257, h27248, hlam]
                          · linarith only [h19744, h27248, hlam]
                        · linarith only [h27247, h4, hlam]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    rcases p27212_3 (m.d 0 2) (by simp) with h27252 | h27252
                    · linarith only [h22010, h27252, hlam]
                    · linarith only [h0, h27252, hlam]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h26256, hlam, p27212_0]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [h0, h19744, hc12, hc25, hlam, hphi, p27212_1]
                  · have p27212_0 := h27212c.1
                    have p27212_1 := h27212c.2.1
                    have p27212_2 := h27212c.2.2.1
                    have p27212_3 := h27212c.2.2.2
                    linarith only [hlam, p27212_0]
      · linarith only [h27063, hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      rcases p27054_3 (m.d 0 1) (by simp) with h27259 | h27259
      · rcases p27054_3 (m.d 1 2) (by simp) with h27260 | h27260
        · linarith only [h0, h27260, hlam]
        · rcases p27054_3 (m.d 1 3) (by simp) with h27262 | h27262
          · linarith only [h1, h27262, hlam]
          · linarith only [h26251, h27262, hlam]
      · linarith only [h27259, hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      rcases p27054_3 (m.d 0 1) (by simp) with h27266 | h27266
      · rcases p27054_3 (m.d 1 2) (by simp) with h27267 | h27267
        · linarith only [h0, h27267, hlam]
        · rcases p27054_3 (m.d 1 3) (by simp) with h27269 | h27269
          · linarith only [h1, h27269, hlam]
          · linarith only [h26252, h27269, hlam]
      · linarith only [h27266, hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h0, hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h26245, hlam, p27054_1]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h26247, hlam, p27054_1]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h26249, hlam, p27054_1]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h1, hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      rcases p27054_3 (m.d 0 1) (by simp) with h27279 | h27279
      · rcases p27054_3 (m.d 1 2) (by simp) with h27280 | h27280
        · linarith only [h26245, h27280, hlam]
        · rcases p27054_3 (m.d 1 3) (by simp) with h27282 | h27282
          · rcases p27054_3 (m.d 1 4) (by simp) with h27283 | h27283
            · linarith only [h26251, h27283, hlam]
            · linarith only [h26247, h27283, hlam]
          · linarith only [h26245, h27282, hlam]
      · linarith only [h0, h27279, hlam]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      rcases p27054_3 (m.d 0 1) (by simp) with h27289 | h27289
      · rcases p27054_3 (m.d 1 2) (by simp) with h27290 | h27290
        · linarith only [h26245, h27290, hlam]
        · rcases p27054_3 (m.d 1 3) (by simp) with h27292 | h27292
          · rcases p27054_3 (m.d 1 4) (by simp) with h27293 | h27293
            · linarith only [h26251, h27293, hlam]
            · rcases p27054_3 (m.d 1 5) (by simp) with h27295 | h27295
              · linarith only [h26252, h27295, hlam]
              · linarith only [h26253, h27295, hlam]
          · linarith only [h26251, h27292, hlam]
      · linarith only [h2, h27289, hlam]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      rcases p27054_3 (m.d 0 1) (by simp) with h27300 | h27300
      · rcases p27054_3 (m.d 1 2) (by simp) with h27301 | h27301
        · linarith only [h26245, h27301, hlam]
        · rcases p27054_3 (m.d 1 3) (by simp) with h27303 | h27303
          · rcases p27054_3 (m.d 1 4) (by simp) with h27304 | h27304
            · linarith only [h26251, h27304, hlam]
            · rcases p27054_3 (m.d 1 5) (by simp) with h27306 | h27306
              · linarith only [h26252, h27306, hlam]
              · rcases h1emax with h27308 | h27308 | h27308 | h27308 | h27308
                · linarith only [h1, h26253, h27308, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p27054_1]
                · rcases h2bigk with h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c | h27310c
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h19744, hc12, hc24, hlam, hphi, p27310_1]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h4, hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h19744, hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h22010, hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h0, hlam, p27310_1]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h26245, hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h26247, hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h26249, hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    rcases p27310_3 (m.d 0 2) (by simp) with h27321 | h27321
                    · linarith only [h27321, hlam, p27310_0]
                    · rcases p27310_3 (m.d 1 2) (by simp) with h27323 | h27323
                      · linarith only [h26245, h27323, hlam]
                      · rcases p27310_3 (m.d 2 3) (by simp) with h27325 | h27325
                        · rcases p27310_3 (m.d 2 4) (by simp) with h27326 | h27326
                          · linarith only [h26255, h27326, hlam]
                          · linarith only [h19744, h27326, hlam]
                        · linarith only [h27325, hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    rcases p27310_3 (m.d 0 2) (by simp) with h27330 | h27330
                    · linarith only [h27330, h4, hlam]
                    · linarith only [h0, h27330, hlam]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h19744, hc02, hc23, hlam, hphi, p27310_1]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27310_1]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h0, h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27310_1]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27310_1]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h26255, hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h26257, hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    rcases p27310_3 (m.d 0 2) (by simp) with h27341 | h27341
                    · linarith only [h27341, hlam, p27310_0]
                    · rcases p27310_3 (m.d 1 2) (by simp) with h27343 | h27343
                      · linarith only [h26249, h27343, hlam]
                      · rcases p27310_3 (m.d 2 3) (by simp) with h27345 | h27345
                        · rcases p27310_3 (m.d 2 4) (by simp) with h27346 | h27346
                          · linarith only [h26257, h27346, hlam]
                          · linarith only [h19744, h27346, hlam]
                        · linarith only [h27345, h4, hlam]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    rcases p27310_3 (m.d 0 2) (by simp) with h27350 | h27350
                    · linarith only [h22010, h27350, hlam]
                    · linarith only [h0, h27350, hlam]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h26256, hlam, p27310_0]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [h0, h19744, hc12, hc25, hlam, hphi, p27310_1]
                  · have p27310_0 := h27310c.1
                    have p27310_1 := h27310c.2.1
                    have p27310_2 := h27310c.2.2.1
                    have p27310_3 := h27310c.2.2.2
                    linarith only [hlam, p27310_0]
                · linarith only [h26247, h26253, h27308, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p27054_1]
                · rcases h2bigk with h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c | h27357c
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h19744, hc12, hc24, hlam, hphi, p27357_1]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h4, hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h19744, hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h22010, hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h0, hlam, p27357_1]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h26245, hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h26247, hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h26249, hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    rcases p27357_3 (m.d 0 2) (by simp) with h27368 | h27368
                    · linarith only [h27368, hlam, p27357_0]
                    · rcases p27357_3 (m.d 1 2) (by simp) with h27370 | h27370
                      · linarith only [h26245, h27370, hlam]
                      · rcases p27357_3 (m.d 2 3) (by simp) with h27372 | h27372
                        · rcases p27357_3 (m.d 2 4) (by simp) with h27373 | h27373
                          · linarith only [h26255, h27373, hlam]
                          · linarith only [h19744, h27373, hlam]
                        · linarith only [h27372, hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    rcases p27357_3 (m.d 0 2) (by simp) with h27377 | h27377
                    · linarith only [h27377, h4, hlam]
                    · linarith only [h0, h27377, hlam]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h19744, hc02, hc23, hlam, hphi, p27357_1]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27357_1]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h0, h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27357_1]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27357_1]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h26255, hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h26257, hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    rcases p27357_3 (m.d 0 2) (by simp) with h27388 | h27388
                    · linarith only [h27388, hlam, p27357_0]
                    · rcases p27357_3 (m.d 1 2) (by simp) with h27390 | h27390
                      · linarith only [h26249, h27390, hlam]
                      · rcases p27357_3 (m.d 2 3) (by simp) with h27392 | h27392
                        · rcases p27357_3 (m.d 2 4) (by simp) with h27393 | h27393
                          · linarith only [h26257, h27393, hlam]
                          · linarith only [h19744, h27393, hlam]
                        · linarith only [h27392, h4, hlam]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    rcases p27357_3 (m.d 0 2) (by simp) with h27397 | h27397
                    · linarith only [h22010, h27397, hlam]
                    · linarith only [h0, h27397, hlam]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h26256, hlam, p27357_0]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [h0, h19744, hc12, hc25, hlam, hphi, p27357_1]
                  · have p27357_0 := h27357c.1
                    have p27357_1 := h27357c.2.1
                    have p27357_2 := h27357c.2.2.1
                    have p27357_3 := h27357c.2.2.2
                    linarith only [hlam, p27357_0]
                · rcases h2bigk with h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c | h27403c
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h19744, hc12, hc24, hlam, hphi, p27403_1]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h4, hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h19744, hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h22010, hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h0, hlam, p27403_1]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h26245, hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h26247, hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h26249, hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    rcases p27403_3 (m.d 0 2) (by simp) with h27414 | h27414
                    · linarith only [h27414, hlam, p27403_0]
                    · rcases p27403_3 (m.d 1 2) (by simp) with h27416 | h27416
                      · linarith only [h26245, h27416, hlam]
                      · rcases p27403_3 (m.d 2 3) (by simp) with h27418 | h27418
                        · rcases p27403_3 (m.d 2 4) (by simp) with h27419 | h27419
                          · linarith only [h26255, h27419, hlam]
                          · linarith only [h19744, h27419, hlam]
                        · linarith only [h27418, hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    rcases p27403_3 (m.d 0 2) (by simp) with h27423 | h27423
                    · linarith only [h27423, h4, hlam]
                    · linarith only [h0, h27423, hlam]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h19744, hc02, hc23, hlam, hphi, p27403_1]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27403_1]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h0, h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27403_1]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27403_1]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h26255, hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h26257, hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    rcases p27403_3 (m.d 0 2) (by simp) with h27434 | h27434
                    · linarith only [h27434, hlam, p27403_0]
                    · rcases p27403_3 (m.d 1 2) (by simp) with h27436 | h27436
                      · linarith only [h26249, h27436, hlam]
                      · rcases p27403_3 (m.d 2 3) (by simp) with h27438 | h27438
                        · rcases p27403_3 (m.d 2 4) (by simp) with h27439 | h27439
                          · linarith only [h26257, h27439, hlam]
                          · linarith only [h19744, h27439, hlam]
                        · linarith only [h27438, h4, hlam]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    rcases p27403_3 (m.d 0 2) (by simp) with h27443 | h27443
                    · linarith only [h22010, h27443, hlam]
                    · linarith only [h0, h27443, hlam]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h26256, hlam, p27403_0]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [h0, h19744, hc12, hc25, hlam, hphi, p27403_1]
                  · have p27403_0 := h27403c.1
                    have p27403_1 := h27403c.2.1
                    have p27403_2 := h27403c.2.2.1
                    have p27403_3 := h27403c.2.2.2
                    linarith only [hlam, p27403_0]
          · linarith only [h26252, h27303, hlam]
      · linarith only [h27300, h3, hlam]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h2, hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h2, h23339, hc12, hc45, hlam, hphi, ht23, ht34, p27054_1]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h26251, hlam, p27054_1]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h26253, hlam, p27054_1]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h3, hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      rcases p27054_3 (m.d 0 1) (by simp) with h27457 | h27457
      · rcases p27054_3 (m.d 1 2) (by simp) with h27458 | h27458
        · linarith only [h26249, h27458, hlam]
        · rcases p27054_3 (m.d 1 3) (by simp) with h27460 | h27460
          · rcases p27054_3 (m.d 1 4) (by simp) with h27461 | h27461
            · linarith only [h26253, h27461, hlam]
            · linarith only [h26247, h27461, hlam]
          · linarith only [h26245, h27460, hlam]
      · linarith only [h0, h27457, hlam]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [h26252, hlam, p27054_0]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      rcases p27054_3 (m.d 0 1) (by simp) with h27467 | h27467
      · rcases p27054_3 (m.d 1 2) (by simp) with h27468 | h27468
        · linarith only [h26249, h27468, hlam]
        · rcases p27054_3 (m.d 1 3) (by simp) with h27470 | h27470
          · rcases p27054_3 (m.d 1 4) (by simp) with h27471 | h27471
            · linarith only [h26253, h27471, hlam]
            · rcases p27054_3 (m.d 1 5) (by simp) with h27473 | h27473
              · rcases h1emax with h27474 | h27474 | h27474 | h27474 | h27474
                · linarith only [h27474, h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p27054_1]
                · rcases h2bigk with h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c | h27476c
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h4, hc12, hc23, hlam, hphi, p27476_1]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h4, hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h19744, hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h22010, hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h0, hlam, p27476_1]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h26245, hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h26247, hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h26249, hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    rcases p27476_3 (m.d 0 2) (by simp) with h27487 | h27487
                    · linarith only [h27487, hlam, p27476_0]
                    · rcases p27476_3 (m.d 1 2) (by simp) with h27489 | h27489
                      · linarith only [h26245, h27489, hlam]
                      · rcases p27476_3 (m.d 2 3) (by simp) with h27491 | h27491
                        · rcases p27476_3 (m.d 2 4) (by simp) with h27492 | h27492
                          · linarith only [h26255, h27492, hlam]
                          · linarith only [h19744, h27492, hlam]
                        · linarith only [h27491, hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    rcases p27476_3 (m.d 0 2) (by simp) with h27496 | h27496
                    · linarith only [h27496, h4, hlam]
                    · linarith only [h0, h27496, hlam]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h19744, hc02, hc23, hlam, hphi, p27476_1]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h22010, h26247, h3, hc12, hc23, hlam, hphi, p27054_1, p27476_1]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h0, h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27476_1]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27476_1]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h26255, hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h26257, hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    rcases p27476_3 (m.d 0 2) (by simp) with h27507 | h27507
                    · linarith only [h27507, hlam, p27476_0]
                    · rcases p27476_3 (m.d 1 2) (by simp) with h27509 | h27509
                      · linarith only [h26249, h27509, hlam]
                      · rcases p27476_3 (m.d 2 3) (by simp) with h27511 | h27511
                        · rcases p27476_3 (m.d 2 4) (by simp) with h27512 | h27512
                          · linarith only [h26257, h27512, hlam]
                          · linarith only [h19744, h27512, hlam]
                        · linarith only [h27511, h4, hlam]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    rcases p27476_3 (m.d 0 2) (by simp) with h27516 | h27516
                    · linarith only [h22010, h27516, hlam]
                    · linarith only [h0, h27516, hlam]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h26256, hlam, p27476_0]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [h0, h19744, hc12, hc25, hlam, hphi, p27476_1]
                  · have p27476_0 := h27476c.1
                    have p27476_1 := h27476c.2.1
                    have p27476_2 := h27476c.2.2.1
                    have p27476_3 := h27476c.2.2.2
                    linarith only [hlam, p27476_0]
                · linarith only [h26247, h26252, h27474, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p27054_1]
                · rcases h2bigk with h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c | h27523c
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h19744, hc12, hc24, hlam, hphi, p27523_1]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h4, hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h19744, hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h22010, hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h0, hlam, p27523_1]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h26245, hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h26247, hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h26249, hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    rcases p27523_3 (m.d 0 2) (by simp) with h27534 | h27534
                    · linarith only [h27534, hlam, p27523_0]
                    · rcases p27523_3 (m.d 1 2) (by simp) with h27536 | h27536
                      · linarith only [h26245, h27536, hlam]
                      · rcases p27523_3 (m.d 2 3) (by simp) with h27538 | h27538
                        · rcases p27523_3 (m.d 2 4) (by simp) with h27539 | h27539
                          · linarith only [h26255, h27539, hlam]
                          · linarith only [h19744, h27539, hlam]
                        · linarith only [h27538, hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    rcases p27523_3 (m.d 0 2) (by simp) with h27543 | h27543
                    · linarith only [h27543, h4, hlam]
                    · linarith only [h0, h27543, hlam]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h19744, hc02, hc23, hlam, hphi, p27523_1]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27523_1]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h0, h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27523_1]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h26257, hc12, hc45, hlam, hphi, ht23, ht34, p27523_1]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h26255, hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h26257, hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    rcases p27523_3 (m.d 0 2) (by simp) with h27554 | h27554
                    · linarith only [h27554, hlam, p27523_0]
                    · rcases p27523_3 (m.d 1 2) (by simp) with h27556 | h27556
                      · linarith only [h26249, h27556, hlam]
                      · rcases p27523_3 (m.d 2 3) (by simp) with h27558 | h27558
                        · rcases p27523_3 (m.d 2 4) (by simp) with h27559 | h27559
                          · linarith only [h26257, h27559, hlam]
                          · linarith only [h19744, h27559, hlam]
                        · linarith only [h27558, h4, hlam]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    rcases p27523_3 (m.d 0 2) (by simp) with h27563 | h27563
                    · linarith only [h22010, h27563, hlam]
                    · linarith only [h0, h27563, hlam]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h26256, hlam, p27523_0]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [h0, h19744, hc12, hc25, hlam, hphi, p27523_1]
                  · have p27523_0 := h27523c.1
                    have p27523_1 := h27523c.2.1
                    have p27523_2 := h27523c.2.2.1
                    have p27523_3 := h27523c.2.2.2
                    linarith only [hlam, p27523_0]
                · linarith only [h26247, h27474, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p27054_1]
              · linarith only [h26253, h27473, hlam]
          · linarith only [h26251, h27470, hlam]
      · linarith only [h2, h27467, hlam]
    · have p27054_0 := h27054c.1
      have p27054_1 := h27054c.2.1
      have p27054_2 := h27054c.2.2.1
      have p27054_3 := h27054c.2.2.2
      linarith only [hlam, p27054_0]

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x0_x0 (m : N7Model)
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
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h26252 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h26253 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26255 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26256 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h26257 | h26257
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251 h26252 h26253 h26255 h26256 h26257
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251 h26252 h26253 h26255 h26256 h26257

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x0_x1 (m : N7Model)
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
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h26252 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h26253 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26255 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26256 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  linarith only [h23338, h26256, h4, hlam]

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x0 (m : N7Model)
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
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h26252 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h26253 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26255 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h26256 | h26256
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251 h26252 h26253 h26255 h26256
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251 h26252 h26253 h26255 h26256

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x1 (m : N7Model)
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
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h26252 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h26253 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26255 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  linarith only [h23337, h26255, h4, hlam]

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1 (m : N7Model)
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
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h26252 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h26253 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h26255 | h26255
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251 h26252 h26253 h26255
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251 h26252 h26253 h26255

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0 (m : N7Model)
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
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h26252 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  rcases m.htr 1 4 5 (by decide) (by decide) with h26253 | h26253
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251 h26252 h26253
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251 h26252 h26253

end R2N4
