import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S13
import Jsp000404.R1LeavesN7_10S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9868 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9869 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9870 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9871 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9872 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 2 3 4 (by decide) (by decide) with h10283 | h10283
  · rcases m.htr 2 3 5 (by decide) (by decide) with h10284 | h10284
    · rcases m.htr 2 4 5 (by decide) (by decide) with h10285 | h10285
      · linarith only [h10285, h6874, h9872, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h10287 | h10287
        · linarith only [h10283, h10287, h6874, h8887, h9872, hlam]
        · rcases h2bigk with h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c | h10289c
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h0, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            rcases p10289_3 (m.d 0 2) (by simp) with h10292 | h10292
            · rcases p10289_3 (m.d 1 2) (by simp) with h10293 | h10293
              · rcases p10289_3 (m.d 2 3) (by simp) with h10294 | h10294
                · linarith only [h10294, hlam, p10289_0]
                · rcases p10289_3 (m.d 2 4) (by simp) with h10296 | h10296
                  · linarith only [h10296, h8887, hlam]
                  · rcases p10289_3 (m.d 2 5) (by simp) with h10298 | h10298
                    · linarith only [h10298, h8888, hlam]
                    · rcases h4bigk with h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c | h10300c
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h6874, hlam, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h6874, h9872, hc24, hc45, hlam, hphi, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h6874, h9872, hc34, hc45, hlam, hphi, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h8890, hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h9872, hc04, hc45, hlam, hphi, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h9872, hc24, hc45, hlam, hphi, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h9872, hc34, hc45, hlam, hphi, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h9872, hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h8887, hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h9869, hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h0, h8887, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h10285, hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h8889, hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h9871, hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h10283, hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h10287, hlam, p10300_0]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [hc14, hc45, hlam, hphi, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [h10283, hc34, hc45, hlam, hphi, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [hc34, hc45, hlam, hphi, p10300_1]
                      · have p10300_0 := h10300c.1
                        have p10300_1 := h10300c.2.1
                        have p10300_2 := h10300c.2.2.1
                        have p10300_3 := h10300c.2.2.2
                        linarith only [hlam, p10300_0]
              · linarith only [h10293, h9868, hlam]
            · linarith only [h10292, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            rcases p10289_3 (m.d 0 2) (by simp) with h10328 | h10328
            · rcases p10289_3 (m.d 1 2) (by simp) with h10329 | h10329
              · rcases p10289_3 (m.d 2 3) (by simp) with h10330 | h10330
                · linarith only [h10330, h8886, hlam]
                · linarith only [h10283, h10330, hlam]
              · linarith only [h10329, h9869, hlam]
            · linarith only [h10328, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            rcases p10289_3 (m.d 0 2) (by simp) with h10335 | h10335
            · rcases p10289_3 (m.d 1 2) (by simp) with h10336 | h10336
              · rcases p10289_3 (m.d 2 3) (by simp) with h10337 | h10337
                · linarith only [h10337, h8886, hlam]
                · linarith only [h10284, h10337, hlam]
              · linarith only [h10336, h9870, hlam]
            · linarith only [h10335, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h10284, h8886, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10289_1]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            rcases p10289_3 (m.d 0 2) (by simp) with h10344 | h10344
            · linarith only [h0, h10344, hlam]
            · linarith only [h10344, h8886, hlam]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            rcases p10289_3 (m.d 0 2) (by simp) with h10347 | h10347
            · linarith only [h0, h10347, hlam]
            · linarith only [h10347, h8887, hlam]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            rcases p10289_3 (m.d 0 2) (by simp) with h10350 | h10350
            · linarith only [h0, h10350, hlam]
            · linarith only [h10350, h8888, hlam]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h8886, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h9868, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            rcases p10289_3 (m.d 0 2) (by simp) with h10356 | h10356
            · rcases p10289_3 (m.d 1 2) (by simp) with h10357 | h10357
              · rcases p10289_3 (m.d 2 3) (by simp) with h10358 | h10358
                · rcases p10289_3 (m.d 2 4) (by simp) with h10359 | h10359
                  · linarith only [h10283, h10359, hlam]
                  · rcases p10289_3 (m.d 2 5) (by simp) with h10361 | h10361
                    · linarith only [h10284, h10361, hlam]
                    · linarith only [h10285, h10361, hlam]
                · linarith only [h10283, h10358, hlam]
              · linarith only [h10357, h9869, hlam]
            · linarith only [h10356, h8887, hlam]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            rcases p10289_3 (m.d 0 2) (by simp) with h10367 | h10367
            · rcases p10289_3 (m.d 1 2) (by simp) with h10368 | h10368
              · rcases p10289_3 (m.d 2 3) (by simp) with h10369 | h10369
                · rcases p10289_3 (m.d 2 4) (by simp) with h10370 | h10370
                  · linarith only [h10283, h10370, hlam]
                  · rcases p10289_3 (m.d 2 5) (by simp) with h10372 | h10372
                    · linarith only [h10284, h10372, hlam]
                    · rcases h4bigk with h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c | h10374c
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h6874, hlam, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h10283, h8890, hc34, hc45, hlam, hphi, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h8890, hc34, hc45, hlam, hphi, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h8890, hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h6874, hc01, hc14, hlam, hphi, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h10283, h9872, hc34, hc45, hlam, hphi, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h9872, hc34, hc45, hlam, hphi, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h9872, hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h8887, hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h9869, hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h8887, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h10285, hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h8889, hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h9871, hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h10283, hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h10287, hlam, p10374_0]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [hc14, hc45, hlam, hphi, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [hc24, hc45, hlam, hphi, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [hc34, hc45, hlam, hphi, p10374_1]
                      · have p10374_0 := h10374c.1
                        have p10374_1 := h10374c.2.1
                        have p10374_2 := h10374c.2.2.1
                        have p10374_3 := h10374c.2.2.2
                        linarith only [hlam, p10374_0]
                · linarith only [h10284, h10369, hlam]
              · linarith only [h10368, h9870, hlam]
            · linarith only [h10367, h8888, hlam]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h8887, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h9869, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h10283, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h10285, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h8888, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h9870, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [h10284, hlam, p10289_0]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            rcases p10289_3 (m.d 0 2) (by simp) with h10411 | h10411
            · rcases p10289_3 (m.d 1 2) (by simp) with h10412 | h10412
              · rcases p10289_3 (m.d 2 3) (by simp) with h10413 | h10413
                · rcases p10289_3 (m.d 2 4) (by simp) with h10414 | h10414
                  · linarith only [h10285, h10414, hlam]
                  · rcases p10289_3 (m.d 2 5) (by simp) with h10416 | h10416
                    · rcases h4bigk with h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h6874, hlam, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h10283, h8890, hc34, hc45, hlam, hphi, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h8890, hc34, hc45, hlam, hphi, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h8890, hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h6874, hc01, hc14, hlam, hphi, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h10283, h9872, hc34, hc45, hlam, hphi, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h9872, hc34, hc45, hlam, hphi, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h9872, hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h8887, hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h9869, hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h8888, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p10289_1, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h10285, hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h8889, hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h9871, hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h10283, hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h10287, hlam, p10417_0]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [hc14, hc45, hlam, hphi, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [hc24, hc45, hlam, hphi, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [hc34, hc45, hlam, hphi, p10417_1]
                      · have p10417_0 := h10417c.1
                        have p10417_1 := h10417c.2.1
                        have p10417_2 := h10417c.2.2.1
                        have p10417_3 := h10417c.2.2.2
                        linarith only [hlam, p10417_0]
                    · linarith only [h10285, h10416, hlam]
                · linarith only [h10283, h10413, hlam]
              · linarith only [h10412, h9869, hlam]
            · linarith only [h10411, h8887, hlam]
          · have p10289_0 := h10289c.1
            have p10289_1 := h10289c.2.1
            have p10289_2 := h10289c.2.2.1
            have p10289_3 := h10289c.2.2.2
            linarith only [hlam, p10289_0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h10448 | h10448
      · linarith only [h10448, h8887, h8890, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h10450 | h10450
        · linarith only [h10283, h10450, h6874, h9872, hc01, hc23, hlam, hphi, ht12]
        · rcases h2bigk with h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c | h10452c
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h0, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            rcases p10452_3 (m.d 0 2) (by simp) with h10455 | h10455
            · rcases p10452_3 (m.d 1 2) (by simp) with h10456 | h10456
              · rcases p10452_3 (m.d 2 3) (by simp) with h10457 | h10457
                · linarith only [h10457, hlam, p10452_0]
                · rcases p10452_3 (m.d 2 4) (by simp) with h10459 | h10459
                  · linarith only [h10459, h8887, hlam]
                  · rcases p10452_3 (m.d 2 5) (by simp) with h10461 | h10461
                    · linarith only [h10461, h8888, hlam]
                    · linarith only [h10284, h10461, hlam]
              · linarith only [h10456, h9868, hlam]
            · linarith only [h10455, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            rcases p10452_3 (m.d 0 2) (by simp) with h10466 | h10466
            · rcases p10452_3 (m.d 1 2) (by simp) with h10467 | h10467
              · rcases p10452_3 (m.d 2 3) (by simp) with h10468 | h10468
                · linarith only [h10468, h8886, hlam]
                · linarith only [h10283, h10468, hlam]
              · linarith only [h10467, h9869, hlam]
            · linarith only [h10466, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            rcases p10452_3 (m.d 0 2) (by simp) with h10473 | h10473
            · rcases p10452_3 (m.d 1 2) (by simp) with h10474 | h10474
              · rcases p10452_3 (m.d 2 3) (by simp) with h10475 | h10475
                · linarith only [h10475, h8886, hlam]
                · rcases p10452_3 (m.d 2 4) (by simp) with h10477 | h10477
                  · linarith only [h10477, h8887, hlam]
                  · rcases p10452_3 (m.d 2 5) (by simp) with h10479 | h10479
                    · linarith only [h10479, hlam, p10452_0]
                    · rcases h4bigk with h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c | h10481c
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h6874, hlam, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h8890, hc24, hc45, hlam, hphi, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h8890, hc34, hc45, hlam, hphi, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h8890, hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h6874, hc01, hc14, hlam, hphi, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h9872, hc24, hc45, hlam, hphi, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h9872, hc34, hc45, hlam, hphi, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h9872, hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h8887, hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h9869, hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h0, h8887, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h10448, hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h8889, hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h9871, hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h10283, hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h10450, hlam, p10481_0]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [hc14, hc45, hlam, hphi, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [h10283, hc34, hc45, hlam, hphi, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [hc34, hc45, hlam, hphi, p10481_1]
                      · have p10481_0 := h10481c.1
                        have p10481_1 := h10481c.2.1
                        have p10481_2 := h10481c.2.2.1
                        have p10481_3 := h10481c.2.2.2
                        linarith only [hlam, p10481_0]
              · linarith only [h10474, h9870, hlam]
            · linarith only [h10473, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h10283, h8886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10452_1]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            rcases p10452_3 (m.d 0 2) (by simp) with h10511 | h10511
            · linarith only [h0, h10511, hlam]
            · linarith only [h10511, h8886, hlam]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            rcases p10452_3 (m.d 0 2) (by simp) with h10514 | h10514
            · linarith only [h0, h10514, hlam]
            · linarith only [h10514, h8887, hlam]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            rcases p10452_3 (m.d 0 2) (by simp) with h10517 | h10517
            · linarith only [h0, h10517, hlam]
            · linarith only [h10517, h8888, hlam]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h8886, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h9868, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h10283, h10284, h10450, hc34, hc45, hlam, hphi, p10452_1]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h10284, hlam, p10452_1]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h8887, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h9869, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h10283, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h10448, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h8888, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h9870, hlam, p10452_0]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [h0, h10283, h8888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10452_1]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            rcases p10452_3 (m.d 0 2) (by simp) with h10533 | h10533
            · rcases p10452_3 (m.d 1 2) (by simp) with h10534 | h10534
              · rcases p10452_3 (m.d 2 3) (by simp) with h10535 | h10535
                · linarith only [h10284, h10535, hlam]
                · linarith only [h10283, h10535, hlam]
              · linarith only [h10534, h9869, hlam]
            · linarith only [h10533, h8887, hlam]
          · have p10452_0 := h10452c.1
            have p10452_1 := h10452c.2.1
            have p10452_2 := h10452c.2.2.1
            have p10452_3 := h10452c.2.2.2
            linarith only [hlam, p10452_0]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h10541 | h10541
    · rcases m.htr 2 4 5 (by decide) (by decide) with h10542 | h10542
      · linarith only [h10283, h10541, h10542, h6874, h8889, h9872, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
      · linarith only [h10283, h10541, h10542, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h10545 | h10545
      · linarith only [h10545, h6874, h9872, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h10547 | h10547
        · linarith only [h10547, h6874, h8889, h9872, hlam]
        · rcases h2bigk with h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c | h10549c
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h0, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            rcases p10549_3 (m.d 0 2) (by simp) with h10552 | h10552
            · rcases p10549_3 (m.d 1 2) (by simp) with h10553 | h10553
              · rcases p10549_3 (m.d 2 3) (by simp) with h10554 | h10554
                · linarith only [h10554, hlam, p10549_0]
                · rcases p10549_3 (m.d 2 4) (by simp) with h10556 | h10556
                  · linarith only [h10556, h8887, hlam]
                  · linarith only [h10283, h10556, hlam]
              · linarith only [h10553, h9868, hlam]
            · linarith only [h10552, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            rcases p10549_3 (m.d 0 2) (by simp) with h10561 | h10561
            · rcases p10549_3 (m.d 1 2) (by simp) with h10562 | h10562
              · rcases p10549_3 (m.d 2 3) (by simp) with h10563 | h10563
                · linarith only [h10563, h8886, hlam]
                · rcases p10549_3 (m.d 2 4) (by simp) with h10565 | h10565
                  · linarith only [h10565, hlam, p10549_0]
                  · rcases p10549_3 (m.d 2 5) (by simp) with h10567 | h10567
                    · linarith only [h10567, h8888, hlam]
                    · linarith only [h10545, h10567, hlam]
              · linarith only [h10562, h9869, hlam]
            · linarith only [h10561, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            rcases p10549_3 (m.d 0 2) (by simp) with h10572 | h10572
            · rcases p10549_3 (m.d 1 2) (by simp) with h10573 | h10573
              · rcases p10549_3 (m.d 2 3) (by simp) with h10574 | h10574
                · linarith only [h10574, h8886, hlam]
                · rcases p10549_3 (m.d 2 4) (by simp) with h10576 | h10576
                  · linarith only [h10576, h8887, hlam]
                  · rcases p10549_3 (m.d 2 5) (by simp) with h10578 | h10578
                    · linarith only [h10578, hlam, p10549_0]
                    · rcases h4bigk with h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h6874, hlam, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h6874, h9872, hc24, hc45, hlam, hphi, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h10283, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h8890, hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h9872, hc04, hc45, hlam, hphi, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h9872, hc24, hc45, hlam, hphi, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h10283, h9872, hc23, hc45, hlam, hphi, ht34, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h9872, hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h8887, hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h9869, hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h10283, hlam, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h10545, hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h8889, hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h9871, hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h8886, h8889, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h10547, hlam, p10580_0]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [hc14, hc45, hlam, hphi, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h10283, hc23, hc45, hlam, hphi, ht34, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [h10283, hc23, hc45, hlam, hphi, ht34, p10580_1]
                      · have p10580_0 := h10580c.1
                        have p10580_1 := h10580c.2.1
                        have p10580_2 := h10580c.2.2.1
                        have p10580_3 := h10580c.2.2.2
                        linarith only [hlam, p10580_0]
              · linarith only [h10573, h9870, hlam]
            · linarith only [h10572, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h10283, h8886, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10549_1]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            rcases p10549_3 (m.d 0 2) (by simp) with h10610 | h10610
            · linarith only [h0, h10610, hlam]
            · linarith only [h10610, h8886, hlam]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            rcases p10549_3 (m.d 0 2) (by simp) with h10613 | h10613
            · linarith only [h0, h10613, hlam]
            · linarith only [h10613, h8887, hlam]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            rcases p10549_3 (m.d 0 2) (by simp) with h10616 | h10616
            · linarith only [h0, h10616, hlam]
            · linarith only [h10616, h8888, hlam]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h8886, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h9868, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h10283, hlam, p10549_1]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h10541, hlam, p10549_1]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h8887, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h9869, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h8887, h8890, hc23, hc45, hlam, hphi, ht34, p10549_1]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h10545, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h8888, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [h9870, hlam, p10549_0]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            rcases p10549_3 (m.d 0 2) (by simp) with h10631 | h10631
            · rcases p10549_3 (m.d 1 2) (by simp) with h10632 | h10632
              · rcases p10549_3 (m.d 2 3) (by simp) with h10633 | h10633
                · linarith only [h10541, h10633, hlam]
                · rcases p10549_3 (m.d 2 4) (by simp) with h10635 | h10635
                  · linarith only [h10545, h10635, hlam]
                  · linarith only [h10283, h10635, hlam]
              · linarith only [h10632, h9868, hlam]
            · linarith only [h10631, h8886, hlam]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            rcases p10549_3 (m.d 0 2) (by simp) with h10640 | h10640
            · rcases p10549_3 (m.d 1 2) (by simp) with h10641 | h10641
              · rcases p10549_3 (m.d 2 3) (by simp) with h10642 | h10642
                · linarith only [h10541, h10642, hlam]
                · rcases p10549_3 (m.d 2 4) (by simp) with h10644 | h10644
                  · linarith only [h10545, h10644, hlam]
                  · rcases p10549_3 (m.d 2 5) (by simp) with h10646 | h10646
                    · rcases h4bigk with h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c | h10647c
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h6874, hlam, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h10283, h6874, h9872, hc23, hc45, hlam, hphi, ht34, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h6874, h9872, hc34, hc45, hlam, hphi, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h8890, hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h9872, hc04, hc45, hlam, hphi, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h10283, h9872, hc23, hc45, hlam, hphi, ht34, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h9872, hc34, hc45, hlam, hphi, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h9872, hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h8887, hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h9869, hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h10283, hlam, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h10545, hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h8889, hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h9871, hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h10283, h8889, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h10547, hlam, p10647_0]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [hc14, hc45, hlam, hphi, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h10283, hc23, hc45, hlam, hphi, ht34, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [h10283, hc23, hc45, hlam, hphi, ht34, p10647_1]
                      · have p10647_0 := h10647c.1
                        have p10647_1 := h10647c.2.1
                        have p10647_2 := h10647c.2.2.1
                        have p10647_3 := h10647c.2.2.2
                        linarith only [hlam, p10647_0]
                    · linarith only [h10545, h10646, hlam]
              · linarith only [h10641, h9869, hlam]
            · linarith only [h10640, h8887, hlam]
          · have p10549_0 := h10549c.1
            have p10549_1 := h10549c.2.1
            have p10549_2 := h10549c.2.2.1
            have p10549_3 := h10549c.2.2.2
            linarith only [hlam, p10549_0]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9868 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9869 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9870 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9871 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 4 5 (by decide) (by decide) with h9872 | h9872
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h9868 h9869 h9870 h9871 h9872
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h9868 h9869 h9870 h9871 h9872

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9868 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9869 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9870 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9871 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h6874, h8889, h9871, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9868 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9869 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9870 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 3 4 (by decide) (by decide) with h9871 | h9871
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h9868 h9869 h9870 h9871
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h9868 h9869 h9870 h9871

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9868 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9869 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9870 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h0, h8888, h9870, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9868 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9869 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 2 5 (by decide) (by decide) with h9870 | h9870
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h9868 h9869 h9870
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h9868 h9869 h9870

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9868 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9869 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h0, h8887, h9869, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9868 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 2 4 (by decide) (by decide) with h9869 | h9869
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h9868 h9869
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h9868 h9869

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9868 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h0, h8886, h9868, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 2 3 (by decide) (by decide) with h9868 | h9868
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h9868
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h9868

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 0 4 5 (by decide) (by decide) with h8890 | h8890
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890
  · exact r1l7_12_24_L_I_H_I_s10_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890

end R2N4
