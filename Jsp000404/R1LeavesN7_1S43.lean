import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S42

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28286 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h28287 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h28288 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h28289 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h28290 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 1 3 5 (by decide) (by decide) with h28506 | h28506
  · linarith only [h15532, h27842, h28290, h28506, hc01, hc34, hlam, hphi, ht12, ht23]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h28508 | h28508
    · rcases m.htr 2 3 4 (by decide) (by decide) with h28509 | h28509
      · linarith only [h15532, h28290, h28509, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h28511 | h28511
        · linarith only [h15532, h28506, h28511, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h28513 | h28513
          · rcases m.htr 3 4 5 (by decide) (by decide) with h28514 | h28514
            · rcases h0bigk with h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c | h28515c
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [hlam, p28515_0]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h0, hlam, p28515_1]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h15532, hlam, p28515_0]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h18443, hlam, p28515_1]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h20697, hlam, p28515_1]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                rcases p28515_3 (m.d 0 1) (by simp) with h28521 | h28521
                · linarith only [h0, h28521, hlam]
                · rcases p28515_3 (m.d 0 2) (by simp) with h28523 | h28523
                  · rcases p28515_3 (m.d 0 3) (by simp) with h28524 | h28524
                    · linarith only [h22350, h28524, hlam]
                    · linarith only [h15532, h28524, hlam]
                  · linarith only [h0, h28523, hlam]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [hlam, p28515_0]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                rcases p28515_3 (m.d 0 1) (by simp) with h28529 | h28529
                · linarith only [h0, h28529, hlam]
                · rcases p28515_3 (m.d 0 2) (by simp) with h28531 | h28531
                  · rcases p28515_3 (m.d 0 3) (by simp) with h28532 | h28532
                    · linarith only [h22350, h28532, hlam]
                    · rcases p28515_3 (m.d 0 4) (by simp) with h28534 | h28534
                      · linarith only [h22351, h28534, hlam]
                      · linarith only [h22353, h28534, hlam]
                  · linarith only [h22350, h28531, hlam]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                rcases p28515_3 (m.d 0 1) (by simp) with h28538 | h28538
                · linarith only [h0, h28538, hlam]
                · rcases p28515_3 (m.d 0 2) (by simp) with h28540 | h28540
                  · rcases p28515_3 (m.d 0 3) (by simp) with h28541 | h28541
                    · linarith only [h22350, h28541, hlam]
                    · rcases p28515_3 (m.d 0 4) (by simp) with h28543 | h28543
                      · linarith only [h22351, h28543, hlam]
                      · rcases p28515_3 (m.d 0 5) (by simp) with h28545 | h28545
                        · linarith only [h22352, h28545, hlam]
                        · rcases h2bigk with h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c | h28547c
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h0, hlam, p28547_1]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            rcases p28547_3 (m.d 0 2) (by simp) with h28550 | h28550
                            · rcases p28547_3 (m.d 1 2) (by simp) with h28551 | h28551
                              · rcases p28547_3 (m.d 2 3) (by simp) with h28552 | h28552
                                · linarith only [h28552, hlam, p28547_0]
                                · rcases p28547_3 (m.d 2 4) (by simp) with h28554 | h28554
                                  · linarith only [h22351, h28554, hlam]
                                  · linarith only [h28509, h28554, hlam]
                              · linarith only [h28287, h28551, hlam]
                            · linarith only [h28550, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            rcases p28547_3 (m.d 0 2) (by simp) with h28559 | h28559
                            · rcases p28547_3 (m.d 1 2) (by simp) with h28560 | h28560
                              · rcases p28547_3 (m.d 2 3) (by simp) with h28561 | h28561
                                · linarith only [h22350, h28561, hlam]
                                · rcases p28547_3 (m.d 2 4) (by simp) with h28563 | h28563
                                  · linarith only [h28563, hlam, p28547_0]
                                  · rcases p28547_3 (m.d 2 5) (by simp) with h28565 | h28565
                                    · linarith only [h22352, h28565, hlam]
                                    · rcases h3bigk with h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c | h28567c
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h15532, hlam, p28567_1]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h15532, h28506, h28514, hc23, hc34, hlam, hphi, p28567_1]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h22353, hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h27842, hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h28506, h28514, hc03, hc34, hlam, hphi, p28567_1]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h28506, h28514, hc23, hc34, hlam, hphi, p28567_1]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h28290, hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h28506, hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h22350, hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h28287, hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h28509, hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h28511, hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        rcases p28567_3 (m.d 0 3) (by simp) with h28583 | h28583
                                        · linarith only [h28583, hlam, p28567_0]
                                        · rcases p28567_3 (m.d 1 3) (by simp) with h28585 | h28585
                                          · linarith only [h28290, h28585, hlam]
                                          · linarith only [h15532, h28585, hlam]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h15532, hc01, hc34, hlam, hphi, ht12, ht23, p28567_1]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        rcases p28567_3 (m.d 0 3) (by simp) with h28589 | h28589
                                        · linarith only [h22353, h28589, hlam]
                                        · linarith only [h22350, h28589, hlam]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h20697, h28506, hc01, hc34, hlam, hphi, ht12, ht23, p28567_1]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        rcases p28567_3 (m.d 0 3) (by simp) with h28594 | h28594
                                        · linarith only [h28594, hlam, p28567_0]
                                        · rcases p28567_3 (m.d 1 3) (by simp) with h28596 | h28596
                                          · linarith only [h28506, h28596, hlam]
                                          · linarith only [h15532, h28596, hlam]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h15532, hc01, hc35, hlam, hphi, ht12, ht23, p28567_1]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        rcases p28567_3 (m.d 0 3) (by simp) with h28600 | h28600
                                        · linarith only [h27842, h28600, hlam]
                                        · linarith only [h22350, h28600, hlam]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [h28514, hlam, p28567_0]
                                      · have p28567_0 := h28567c.1
                                        have p28567_1 := h28567c.2.1
                                        have p28567_2 := h28567c.2.2.1
                                        have p28567_3 := h28567c.2.2.2
                                        linarith only [hlam, p28567_0]
                              · linarith only [h28288, h28560, hlam]
                            · linarith only [h28559, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            rcases p28547_3 (m.d 0 2) (by simp) with h28607 | h28607
                            · rcases p28547_3 (m.d 1 2) (by simp) with h28608 | h28608
                              · rcases p28547_3 (m.d 2 3) (by simp) with h28609 | h28609
                                · linarith only [h22350, h28609, hlam]
                                · rcases p28547_3 (m.d 2 4) (by simp) with h28611 | h28611
                                  · linarith only [h22351, h28611, hlam]
                                  · linarith only [h28513, h28611, hlam]
                              · linarith only [h28289, h28608, hlam]
                            · linarith only [h28607, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p28515_1, p28547_1]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            rcases p28547_3 (m.d 0 2) (by simp) with h28618 | h28618
                            · linarith only [h0, h28618, hlam]
                            · linarith only [h22350, h28618, hlam]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            rcases p28547_3 (m.d 0 2) (by simp) with h28621 | h28621
                            · linarith only [h0, h28621, hlam]
                            · linarith only [h22351, h28621, hlam]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            rcases p28547_3 (m.d 0 2) (by simp) with h28624 | h28624
                            · linarith only [h0, h28624, hlam]
                            · linarith only [h22352, h28624, hlam]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h22350, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h28287, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h28509, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h28511, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h22351, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h28288, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h22351, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28515_1, p28547_1]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h0, h22351, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p28515_1, p28547_1]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h22352, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h28289, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h0, h22352, h28286, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p28515_1, p28547_1]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [h28513, hlam, p28547_0]
                          · have p28547_0 := h28547c.1
                            have p28547_1 := h28547c.2.1
                            have p28547_2 := h28547c.2.2.1
                            have p28547_3 := h28547c.2.2.2
                            linarith only [hlam, p28547_0]
                  · linarith only [h22351, h28540, hlam]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                rcases p28515_3 (m.d 0 1) (by simp) with h28643 | h28643
                · linarith only [h0, h28643, hlam]
                · rcases p28515_3 (m.d 0 2) (by simp) with h28645 | h28645
                  · rcases p28515_3 (m.d 0 3) (by simp) with h28646 | h28646
                    · linarith only [h22350, h28646, hlam]
                    · rcases p28515_3 (m.d 0 4) (by simp) with h28648 | h28648
                      · linarith only [h22351, h28648, hlam]
                      · linarith only [h28286, h28648, hlam]
                  · linarith only [h22352, h28645, hlam]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h22353, hc01, hc34, hlam, hphi, ht12, ht23, p28515_1]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h22350, hlam, p28515_1]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [hlam, p28515_0]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h22353, hlam, p28515_1]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h27842, hlam, p28515_1]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                rcases p28515_3 (m.d 0 1) (by simp) with h28657 | h28657
                · linarith only [h18443, h28657, hlam]
                · rcases p28515_3 (m.d 0 2) (by simp) with h28659 | h28659
                  · rcases p28515_3 (m.d 0 3) (by simp) with h28660 | h28660
                    · linarith only [h22353, h28660, hlam]
                    · linarith only [h15532, h28660, hlam]
                  · linarith only [h0, h28659, hlam]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h22351, hlam, p28515_0]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                rcases p28515_3 (m.d 0 1) (by simp) with h28665 | h28665
                · linarith only [h18443, h28665, hlam]
                · rcases p28515_3 (m.d 0 2) (by simp) with h28667 | h28667
                  · rcases p28515_3 (m.d 0 3) (by simp) with h28668 | h28668
                    · linarith only [h22353, h28668, hlam]
                    · rcases p28515_3 (m.d 0 4) (by simp) with h28670 | h28670
                      · rcases p28515_3 (m.d 0 5) (by simp) with h28671 | h28671
                        · linarith only [h28286, h28671, hlam]
                        · linarith only [h27842, h28671, hlam]
                      · linarith only [h22353, h28670, hlam]
                  · linarith only [h22350, h28667, hlam]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [hlam, p28515_0]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                rcases p28515_3 (m.d 0 1) (by simp) with h28677 | h28677
                · linarith only [h18443, h28677, hlam]
                · rcases p28515_3 (m.d 0 2) (by simp) with h28679 | h28679
                  · rcases p28515_3 (m.d 0 3) (by simp) with h28680 | h28680
                    · linarith only [h22353, h28680, hlam]
                    · rcases p28515_3 (m.d 0 4) (by simp) with h28682 | h28682
                      · rcases p28515_3 (m.d 0 5) (by simp) with h28683 | h28683
                        · linarith only [h28286, h28683, hlam]
                        · rcases h2bigk with h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c | h28685c
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h0, hlam, p28685_1]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            rcases p28685_3 (m.d 0 2) (by simp) with h28688 | h28688
                            · rcases p28685_3 (m.d 1 2) (by simp) with h28689 | h28689
                              · rcases p28685_3 (m.d 2 3) (by simp) with h28690 | h28690
                                · linarith only [h28690, hlam, p28685_0]
                                · rcases p28685_3 (m.d 2 4) (by simp) with h28692 | h28692
                                  · linarith only [h22351, h28692, hlam]
                                  · linarith only [h28509, h28692, hlam]
                              · linarith only [h28287, h28689, hlam]
                            · linarith only [h28688, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            rcases p28685_3 (m.d 0 2) (by simp) with h28697 | h28697
                            · rcases p28685_3 (m.d 1 2) (by simp) with h28698 | h28698
                              · rcases p28685_3 (m.d 2 3) (by simp) with h28699 | h28699
                                · linarith only [h22350, h28699, hlam]
                                · rcases p28685_3 (m.d 2 4) (by simp) with h28701 | h28701
                                  · linarith only [h28701, hlam, p28685_0]
                                  · rcases p28685_3 (m.d 2 5) (by simp) with h28703 | h28703
                                    · linarith only [h22352, h28703, hlam]
                                    · rcases h3bigk with h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c | h28705c
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h15532, hlam, p28705_1]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h27842, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28515_1, p28705_1]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h22353, hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h27842, hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h15532, h28290, hc01, hc34, hlam, hphi, ht12, ht23, p28705_1]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h28290, hc23, hc34, hlam, hphi, p28705_1]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h28290, hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h28506, hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h22350, hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h28287, hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h28509, hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h28511, hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        rcases p28705_3 (m.d 0 3) (by simp) with h28721 | h28721
                                        · linarith only [h28721, hlam, p28705_0]
                                        · rcases p28705_3 (m.d 1 3) (by simp) with h28723 | h28723
                                          · linarith only [h28290, h28723, hlam]
                                          · linarith only [h15532, h28723, hlam]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h15532, hc01, hc34, hlam, hphi, ht12, ht23, p28705_1]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        rcases p28705_3 (m.d 0 3) (by simp) with h28727 | h28727
                                        · linarith only [h22353, h28727, hlam]
                                        · linarith only [h22350, h28727, hlam]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h20697, h28506, hc01, hc34, hlam, hphi, ht12, ht23, p28705_1]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        rcases p28705_3 (m.d 0 3) (by simp) with h28732 | h28732
                                        · linarith only [h28732, hlam, p28705_0]
                                        · rcases p28705_3 (m.d 1 3) (by simp) with h28734 | h28734
                                          · linarith only [h28506, h28734, hlam]
                                          · linarith only [h15532, h28734, hlam]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h15532, hc01, hc35, hlam, hphi, ht12, ht23, p28705_1]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        rcases p28705_3 (m.d 0 3) (by simp) with h28738 | h28738
                                        · linarith only [h27842, h28738, hlam]
                                        · linarith only [h22350, h28738, hlam]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [h28514, hlam, p28705_0]
                                      · have p28705_0 := h28705c.1
                                        have p28705_1 := h28705c.2.1
                                        have p28705_2 := h28705c.2.2.1
                                        have p28705_3 := h28705c.2.2.2
                                        linarith only [hlam, p28705_0]
                              · linarith only [h28288, h28698, hlam]
                            · linarith only [h28697, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            rcases p28685_3 (m.d 0 2) (by simp) with h28745 | h28745
                            · rcases p28685_3 (m.d 1 2) (by simp) with h28746 | h28746
                              · rcases p28685_3 (m.d 2 3) (by simp) with h28747 | h28747
                                · linarith only [h22350, h28747, hlam]
                                · rcases p28685_3 (m.d 2 4) (by simp) with h28749 | h28749
                                  · linarith only [h22351, h28749, hlam]
                                  · linarith only [h28513, h28749, hlam]
                              · linarith only [h28289, h28746, hlam]
                            · linarith only [h28745, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h22351, h28513, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p28685_1]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            rcases p28685_3 (m.d 0 2) (by simp) with h28756 | h28756
                            · linarith only [h0, h28756, hlam]
                            · linarith only [h22350, h28756, hlam]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            rcases p28685_3 (m.d 0 2) (by simp) with h28759 | h28759
                            · linarith only [h0, h28759, hlam]
                            · linarith only [h22351, h28759, hlam]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            rcases p28685_3 (m.d 0 2) (by simp) with h28762 | h28762
                            · linarith only [h0, h28762, hlam]
                            · linarith only [h22352, h28762, hlam]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h22350, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h28287, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h28509, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h28511, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h22351, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h28288, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            rcases p28685_3 (m.d 0 2) (by simp) with h28772 | h28772
                            · rcases p28685_3 (m.d 1 2) (by simp) with h28773 | h28773
                              · rcases p28685_3 (m.d 2 3) (by simp) with h28774 | h28774
                                · linarith only [h28509, h28774, hlam]
                                · rcases p28685_3 (m.d 2 4) (by simp) with h28776 | h28776
                                  · rcases p28685_3 (m.d 2 5) (by simp) with h28777 | h28777
                                    · linarith only [h28513, h28777, hlam]
                                    · linarith only [h28511, h28777, hlam]
                                  · linarith only [h28509, h28776, hlam]
                              · linarith only [h28287, h28773, hlam]
                            · linarith only [h22350, h28772, hlam]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            rcases p28685_3 (m.d 0 2) (by simp) with h28784 | h28784
                            · rcases p28685_3 (m.d 1 2) (by simp) with h28785 | h28785
                              · rcases p28685_3 (m.d 2 3) (by simp) with h28786 | h28786
                                · linarith only [h28509, h28786, hlam]
                                · rcases p28685_3 (m.d 2 4) (by simp) with h28788 | h28788
                                  · rcases p28685_3 (m.d 2 5) (by simp) with h28789 | h28789
                                    · linarith only [h28513, h28789, hlam]
                                    · rcases h3bigk with h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c | h28791c
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h15532, hlam, p28791_1]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h27842, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28515_1, p28791_1]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h22353, hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h27842, hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h15532, h28290, hc01, hc34, hlam, hphi, ht12, ht23, p28791_1]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h28290, hc23, hc34, hlam, hphi, p28791_1]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h28290, hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h28506, hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h22350, hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h28287, hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h28509, hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h28511, hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        rcases p28791_3 (m.d 0 3) (by simp) with h28807 | h28807
                                        · linarith only [h28807, hlam, p28791_0]
                                        · rcases p28791_3 (m.d 1 3) (by simp) with h28809 | h28809
                                          · linarith only [h28290, h28809, hlam]
                                          · linarith only [h15532, h28809, hlam]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h0, h15532, h22351, h28511, hc01, hc12, hc23, hc34, hlam, hphi, p28685_1, p28791_1]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        rcases p28791_3 (m.d 0 3) (by simp) with h28813 | h28813
                                        · linarith only [h22353, h28813, hlam]
                                        · linarith only [h22350, h28813, hlam]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h0, h15532, h22351, h27842, h28511, hc01, hc12, hc23, hc34, hlam, hphi, p28685_1, p28791_1]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        rcases p28791_3 (m.d 0 3) (by simp) with h28818 | h28818
                                        · linarith only [h28818, hlam, p28791_0]
                                        · rcases p28791_3 (m.d 1 3) (by simp) with h28820 | h28820
                                          · linarith only [h28506, h28820, hlam]
                                          · linarith only [h15532, h28820, hlam]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h0, h15532, h22351, h28511, hc01, hc12, hc23, hc35, hlam, hphi, p28685_1, p28791_1]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        rcases p28791_3 (m.d 0 3) (by simp) with h28824 | h28824
                                        · linarith only [h27842, h28824, hlam]
                                        · linarith only [h22350, h28824, hlam]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [h28514, hlam, p28791_0]
                                      · have p28791_0 := h28791c.1
                                        have p28791_1 := h28791c.2.1
                                        have p28791_2 := h28791c.2.2.1
                                        have p28791_3 := h28791c.2.2.2
                                        linarith only [hlam, p28791_0]
                                  · linarith only [h28513, h28788, hlam]
                              · linarith only [h28289, h28785, hlam]
                            · linarith only [h22352, h28784, hlam]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h22352, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h28289, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h18443, h22352, h28290, hc23, hc34, hlam, hphi, p28515_1, p28685_1]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [h28513, hlam, p28685_0]
                          · have p28685_0 := h28685c.1
                            have p28685_1 := h28685c.2.1
                            have p28685_2 := h28685c.2.2.1
                            have p28685_3 := h28685c.2.2.2
                            linarith only [hlam, p28685_0]
                      · linarith only [h28286, h28682, hlam]
                  · linarith only [h22352, h28679, hlam]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                rcases p28515_3 (m.d 0 1) (by simp) with h28839 | h28839
                · linarith only [h20697, h28839, hlam]
                · rcases p28515_3 (m.d 0 2) (by simp) with h28841 | h28841
                  · rcases p28515_3 (m.d 0 3) (by simp) with h28842 | h28842
                    · linarith only [h27842, h28842, hlam]
                    · linarith only [h15532, h28842, hlam]
                  · linarith only [h0, h28841, hlam]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h22352, hlam, p28515_1]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                rcases p28515_3 (m.d 0 1) (by simp) with h28847 | h28847
                · linarith only [h20697, h28847, hlam]
                · rcases p28515_3 (m.d 0 2) (by simp) with h28849 | h28849
                  · rcases p28515_3 (m.d 0 3) (by simp) with h28850 | h28850
                    · linarith only [h27842, h28850, hlam]
                    · rcases p28515_3 (m.d 0 4) (by simp) with h28852 | h28852
                      · rcases p28515_3 (m.d 0 5) (by simp) with h28853 | h28853
                        · rcases h2bigk with h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c | h28854c
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h0, hlam, p28854_1]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            rcases p28854_3 (m.d 0 2) (by simp) with h28857 | h28857
                            · rcases p28854_3 (m.d 1 2) (by simp) with h28858 | h28858
                              · rcases p28854_3 (m.d 2 3) (by simp) with h28859 | h28859
                                · linarith only [h28859, hlam, p28854_0]
                                · rcases p28854_3 (m.d 2 4) (by simp) with h28861 | h28861
                                  · linarith only [h22351, h28861, hlam]
                                  · linarith only [h28509, h28861, hlam]
                              · linarith only [h28287, h28858, hlam]
                            · linarith only [h28857, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            rcases p28854_3 (m.d 0 2) (by simp) with h28866 | h28866
                            · rcases p28854_3 (m.d 1 2) (by simp) with h28867 | h28867
                              · rcases p28854_3 (m.d 2 3) (by simp) with h28868 | h28868
                                · linarith only [h22350, h28868, hlam]
                                · rcases p28854_3 (m.d 2 4) (by simp) with h28870 | h28870
                                  · linarith only [h28870, hlam, p28854_0]
                                  · rcases p28854_3 (m.d 2 5) (by simp) with h28872 | h28872
                                    · linarith only [h22352, h28872, hlam]
                                    · rcases h3bigk with h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c | h28874c
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h15532, hlam, p28874_1]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h18443, h28286, h28290, hc23, hc34, hlam, hphi, p28515_1, p28874_1]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h22353, hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h27842, hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h15532, h28290, hc01, hc34, hlam, hphi, ht12, ht23, p28874_1]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h28290, hc23, hc34, hlam, hphi, p28874_1]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h28290, hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h28506, hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h22350, hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h28287, hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h28509, hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h28511, hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        rcases p28874_3 (m.d 0 3) (by simp) with h28890 | h28890
                                        · linarith only [h28890, hlam, p28874_0]
                                        · rcases p28874_3 (m.d 1 3) (by simp) with h28892 | h28892
                                          · linarith only [h28290, h28892, hlam]
                                          · linarith only [h15532, h28892, hlam]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h15532, hc01, hc34, hlam, hphi, ht12, ht23, p28874_1]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        rcases p28874_3 (m.d 0 3) (by simp) with h28896 | h28896
                                        · linarith only [h22353, h28896, hlam]
                                        · linarith only [h22350, h28896, hlam]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h15532, h27842, hc01, hc34, hlam, hphi, ht12, ht23, p28874_1]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        rcases p28874_3 (m.d 0 3) (by simp) with h28901 | h28901
                                        · linarith only [h28901, hlam, p28874_0]
                                        · rcases p28874_3 (m.d 1 3) (by simp) with h28903 | h28903
                                          · linarith only [h28506, h28903, hlam]
                                          · linarith only [h15532, h28903, hlam]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h15532, hc01, hc35, hlam, hphi, ht12, ht23, p28874_1]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        rcases p28874_3 (m.d 0 3) (by simp) with h28907 | h28907
                                        · linarith only [h27842, h28907, hlam]
                                        · linarith only [h22350, h28907, hlam]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [h28514, hlam, p28874_0]
                                      · have p28874_0 := h28874c.1
                                        have p28874_1 := h28874c.2.1
                                        have p28874_2 := h28874c.2.2.1
                                        have p28874_3 := h28874c.2.2.2
                                        linarith only [hlam, p28874_0]
                              · linarith only [h28288, h28867, hlam]
                            · linarith only [h28866, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            rcases p28854_3 (m.d 0 2) (by simp) with h28914 | h28914
                            · rcases p28854_3 (m.d 1 2) (by simp) with h28915 | h28915
                              · rcases p28854_3 (m.d 2 3) (by simp) with h28916 | h28916
                                · linarith only [h22350, h28916, hlam]
                                · rcases p28854_3 (m.d 2 4) (by simp) with h28918 | h28918
                                  · linarith only [h22351, h28918, hlam]
                                  · linarith only [h28513, h28918, hlam]
                              · linarith only [h28289, h28915, hlam]
                            · linarith only [h28914, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h15532, h22351, h28286, hc01, hc12, hlam, hphi, p28515_1, p28854_1]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            rcases p28854_3 (m.d 0 2) (by simp) with h28925 | h28925
                            · linarith only [h0, h28925, hlam]
                            · linarith only [h22350, h28925, hlam]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            rcases p28854_3 (m.d 0 2) (by simp) with h28928 | h28928
                            · linarith only [h0, h28928, hlam]
                            · linarith only [h22351, h28928, hlam]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            rcases p28854_3 (m.d 0 2) (by simp) with h28931 | h28931
                            · linarith only [h0, h28931, hlam]
                            · linarith only [h22352, h28931, hlam]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h22350, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h28287, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h28509, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h28511, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h22351, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h28288, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            rcases p28854_3 (m.d 0 2) (by simp) with h28941 | h28941
                            · rcases p28854_3 (m.d 1 2) (by simp) with h28942 | h28942
                              · rcases p28854_3 (m.d 2 3) (by simp) with h28943 | h28943
                                · linarith only [h28509, h28943, hlam]
                                · rcases p28854_3 (m.d 2 4) (by simp) with h28945 | h28945
                                  · rcases p28854_3 (m.d 2 5) (by simp) with h28946 | h28946
                                    · linarith only [h28513, h28946, hlam]
                                    · linarith only [h28511, h28946, hlam]
                                  · linarith only [h28509, h28945, hlam]
                              · linarith only [h28287, h28942, hlam]
                            · linarith only [h22350, h28941, hlam]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            rcases p28854_3 (m.d 0 2) (by simp) with h28953 | h28953
                            · rcases p28854_3 (m.d 1 2) (by simp) with h28954 | h28954
                              · rcases p28854_3 (m.d 2 3) (by simp) with h28955 | h28955
                                · linarith only [h28509, h28955, hlam]
                                · rcases p28854_3 (m.d 2 4) (by simp) with h28957 | h28957
                                  · rcases p28854_3 (m.d 2 5) (by simp) with h28958 | h28958
                                    · linarith only [h28513, h28958, hlam]
                                    · rcases h3bigk with h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c | h28960c
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h15532, hlam, p28960_1]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h28286, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28515_1, p28960_1]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h22353, hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h27842, hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h15532, h28290, hc01, hc34, hlam, hphi, ht12, ht23, p28960_1]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h28290, hc23, hc34, hlam, hphi, p28960_1]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h28290, hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h28506, hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h22350, hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h28287, hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h28509, hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h28511, hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        rcases p28960_3 (m.d 0 3) (by simp) with h28976 | h28976
                                        · linarith only [h28976, hlam, p28960_0]
                                        · rcases p28960_3 (m.d 1 3) (by simp) with h28978 | h28978
                                          · linarith only [h28290, h28978, hlam]
                                          · linarith only [h15532, h28978, hlam]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h0, h15532, h22351, h28511, hc01, hc12, hc23, hc34, hlam, hphi, p28854_1, p28960_1]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        rcases p28960_3 (m.d 0 3) (by simp) with h28982 | h28982
                                        · linarith only [h22353, h28982, hlam]
                                        · linarith only [h22350, h28982, hlam]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h0, h20697, h22351, h28506, h28511, hc01, hc12, hc23, hc34, hlam, hphi, p28854_1, p28960_1]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        rcases p28960_3 (m.d 0 3) (by simp) with h28987 | h28987
                                        · linarith only [h28987, hlam, p28960_0]
                                        · rcases p28960_3 (m.d 1 3) (by simp) with h28989 | h28989
                                          · linarith only [h28506, h28989, hlam]
                                          · linarith only [h15532, h28989, hlam]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h0, h15532, h22351, h28511, hc01, hc12, hc23, hc35, hlam, hphi, p28854_1, p28960_1]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        rcases p28960_3 (m.d 0 3) (by simp) with h28993 | h28993
                                        · linarith only [h27842, h28993, hlam]
                                        · linarith only [h22350, h28993, hlam]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [h28514, hlam, p28960_0]
                                      · have p28960_0 := h28960c.1
                                        have p28960_1 := h28960c.2.1
                                        have p28960_2 := h28960c.2.2.1
                                        have p28960_3 := h28960c.2.2.2
                                        linarith only [hlam, p28960_0]
                                  · linarith only [h28513, h28957, hlam]
                              · linarith only [h28289, h28954, hlam]
                            · linarith only [h22352, h28953, hlam]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h22352, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h28289, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            rcases p28854_3 (m.d 0 2) (by simp) with h29003 | h29003
                            · rcases p28854_3 (m.d 1 2) (by simp) with h29004 | h29004
                              · rcases p28854_3 (m.d 2 3) (by simp) with h29005 | h29005
                                · linarith only [h28511, h29005, hlam]
                                · rcases p28854_3 (m.d 2 4) (by simp) with h29007 | h29007
                                  · rcases p28854_3 (m.d 2 5) (by simp) with h29008 | h29008
                                    · rcases h3bigk with h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c | h29009c
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h15532, hlam, p29009_1]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h18443, h28286, h28290, hc23, hc34, hlam, hphi, p28515_1, p29009_1]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h22353, hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h27842, hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h15532, h28290, hc01, hc34, hlam, hphi, ht12, ht23, p29009_1]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h28290, hc23, hc34, hlam, hphi, p29009_1]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h28290, hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h28506, hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h22350, hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h28287, hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h28509, hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h28511, hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        rcases p29009_3 (m.d 0 3) (by simp) with h29025 | h29025
                                        · linarith only [h29025, hlam, p29009_0]
                                        · rcases p29009_3 (m.d 1 3) (by simp) with h29027 | h29027
                                          · linarith only [h28290, h29027, hlam]
                                          · linarith only [h15532, h29027, hlam]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h0, h15532, h22351, h28513, hc01, hc12, hc23, hc34, hlam, hphi, p28854_1, p29009_1]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        rcases p29009_3 (m.d 0 3) (by simp) with h29031 | h29031
                                        · linarith only [h22353, h29031, hlam]
                                        · linarith only [h22350, h29031, hlam]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h0, h15532, h22351, h27842, h28513, hc01, hc12, hc23, hc34, hlam, hphi, p28854_1, p29009_1]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        rcases p29009_3 (m.d 0 3) (by simp) with h29036 | h29036
                                        · linarith only [h29036, hlam, p29009_0]
                                        · rcases p29009_3 (m.d 1 3) (by simp) with h29038 | h29038
                                          · linarith only [h28506, h29038, hlam]
                                          · linarith only [h15532, h29038, hlam]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h0, h15532, h22351, h28513, hc01, hc12, hc23, hc35, hlam, hphi, p28854_1, p29009_1]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        rcases p29009_3 (m.d 0 3) (by simp) with h29042 | h29042
                                        · linarith only [h27842, h29042, hlam]
                                        · linarith only [h22350, h29042, hlam]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [h28514, hlam, p29009_0]
                                      · have p29009_0 := h29009c.1
                                        have p29009_1 := h29009c.2.1
                                        have p29009_2 := h29009c.2.2.1
                                        have p29009_3 := h29009c.2.2.2
                                        linarith only [hlam, p29009_0]
                                    · linarith only [h28511, h29008, hlam]
                                  · linarith only [h28509, h29007, hlam]
                              · linarith only [h28287, h29004, hlam]
                            · linarith only [h22350, h29003, hlam]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [h28513, hlam, p28854_0]
                          · have p28854_0 := h28854c.1
                            have p28854_1 := h28854c.2.1
                            have p28854_2 := h28854c.2.2.1
                            have p28854_3 := h28854c.2.2.2
                            linarith only [hlam, p28854_0]
                        · linarith only [h27842, h28853, hlam]
                      · linarith only [h22353, h28852, hlam]
                  · linarith only [h22350, h28849, hlam]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [h28286, hlam, p28515_1]
              · have p28515_0 := h28515c.1
                have p28515_1 := h28515c.2.1
                have p28515_2 := h28515c.2.2.1
                have p28515_3 := h28515c.2.2.2
                linarith only [hlam, p28515_0]
            · linarith only [h22353, h28286, h28514, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h29059 | h29059
            · rcases h0bigk with h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c | h29060c
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [hlam, p29060_0]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h0, hlam, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h15532, hlam, p29060_0]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h18443, hlam, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h20697, hlam, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                rcases p29060_3 (m.d 0 1) (by simp) with h29066 | h29066
                · linarith only [h0, h29066, hlam]
                · rcases p29060_3 (m.d 0 2) (by simp) with h29068 | h29068
                  · rcases p29060_3 (m.d 0 3) (by simp) with h29069 | h29069
                    · linarith only [h22350, h29069, hlam]
                    · linarith only [h15532, h29069, hlam]
                  · linarith only [h0, h29068, hlam]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [hlam, p29060_0]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                rcases p29060_3 (m.d 0 1) (by simp) with h29074 | h29074
                · linarith only [h0, h29074, hlam]
                · rcases p29060_3 (m.d 0 2) (by simp) with h29076 | h29076
                  · rcases p29060_3 (m.d 0 3) (by simp) with h29077 | h29077
                    · linarith only [h22350, h29077, hlam]
                    · rcases p29060_3 (m.d 0 4) (by simp) with h29079 | h29079
                      · linarith only [h22351, h29079, hlam]
                      · linarith only [h22353, h29079, hlam]
                  · linarith only [h22350, h29076, hlam]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h28286, h28509, h28513, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                rcases p29060_3 (m.d 0 1) (by simp) with h29084 | h29084
                · linarith only [h0, h29084, hlam]
                · rcases p29060_3 (m.d 0 2) (by simp) with h29086 | h29086
                  · rcases p29060_3 (m.d 0 3) (by simp) with h29087 | h29087
                    · linarith only [h22350, h29087, hlam]
                    · rcases p29060_3 (m.d 0 4) (by simp) with h29089 | h29089
                      · linarith only [h22351, h29089, hlam]
                      · linarith only [h28286, h29089, hlam]
                  · linarith only [h22352, h29086, hlam]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h15532, h28506, h29059, hc01, hc34, hlam, hphi, ht12, ht23, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h22350, hlam, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [hlam, p29060_0]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h22353, hlam, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h27842, hlam, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                rcases p29060_3 (m.d 0 1) (by simp) with h29098 | h29098
                · linarith only [h18443, h29098, hlam]
                · rcases p29060_3 (m.d 0 2) (by simp) with h29100 | h29100
                  · rcases p29060_3 (m.d 0 3) (by simp) with h29101 | h29101
                    · linarith only [h22353, h29101, hlam]
                    · linarith only [h15532, h29101, hlam]
                  · linarith only [h0, h29100, hlam]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h22351, hlam, p29060_0]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                rcases p29060_3 (m.d 0 1) (by simp) with h29106 | h29106
                · linarith only [h18443, h29106, hlam]
                · rcases p29060_3 (m.d 0 2) (by simp) with h29108 | h29108
                  · rcases p29060_3 (m.d 0 3) (by simp) with h29109 | h29109
                    · linarith only [h22353, h29109, hlam]
                    · rcases p29060_3 (m.d 0 4) (by simp) with h29111 | h29111
                      · rcases p29060_3 (m.d 0 5) (by simp) with h29112 | h29112
                        · linarith only [h28286, h29112, hlam]
                        · linarith only [h27842, h29112, hlam]
                      · linarith only [h22353, h29111, hlam]
                  · linarith only [h22350, h29108, hlam]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [hlam, p29060_0]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h22353, h28286, h28509, h28513, hc23, hc34, hlam, hphi, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                rcases p29060_3 (m.d 0 1) (by simp) with h29119 | h29119
                · linarith only [h20697, h29119, hlam]
                · rcases p29060_3 (m.d 0 2) (by simp) with h29121 | h29121
                  · rcases p29060_3 (m.d 0 3) (by simp) with h29122 | h29122
                    · linarith only [h27842, h29122, hlam]
                    · linarith only [h15532, h29122, hlam]
                  · linarith only [h0, h29121, hlam]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h22352, hlam, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                rcases p29060_3 (m.d 0 1) (by simp) with h29127 | h29127
                · linarith only [h20697, h29127, hlam]
                · rcases p29060_3 (m.d 0 2) (by simp) with h29129 | h29129
                  · rcases p29060_3 (m.d 0 3) (by simp) with h29130 | h29130
                    · linarith only [h27842, h29130, hlam]
                    · rcases p29060_3 (m.d 0 4) (by simp) with h29132 | h29132
                      · rcases p29060_3 (m.d 0 5) (by simp) with h29133 | h29133
                        · rcases h2bigk with h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c | h29134c
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h0, hlam, p29134_1]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            rcases p29134_3 (m.d 0 2) (by simp) with h29137 | h29137
                            · rcases p29134_3 (m.d 1 2) (by simp) with h29138 | h29138
                              · rcases p29134_3 (m.d 2 3) (by simp) with h29139 | h29139
                                · linarith only [h29139, hlam, p29134_0]
                                · rcases p29134_3 (m.d 2 4) (by simp) with h29141 | h29141
                                  · linarith only [h22351, h29141, hlam]
                                  · linarith only [h28509, h29141, hlam]
                              · linarith only [h28287, h29138, hlam]
                            · linarith only [h29137, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            rcases p29134_3 (m.d 0 2) (by simp) with h29146 | h29146
                            · rcases p29134_3 (m.d 1 2) (by simp) with h29147 | h29147
                              · rcases p29134_3 (m.d 2 3) (by simp) with h29148 | h29148
                                · linarith only [h22350, h29148, hlam]
                                · rcases p29134_3 (m.d 2 4) (by simp) with h29150 | h29150
                                  · linarith only [h29150, hlam, p29134_0]
                                  · rcases p29134_3 (m.d 2 5) (by simp) with h29152 | h29152
                                    · linarith only [h22352, h29152, hlam]
                                    · linarith only [h28513, h29152, hlam]
                              · linarith only [h28288, h29147, hlam]
                            · linarith only [h29146, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            rcases p29134_3 (m.d 0 2) (by simp) with h29157 | h29157
                            · rcases p29134_3 (m.d 1 2) (by simp) with h29158 | h29158
                              · rcases p29134_3 (m.d 2 3) (by simp) with h29159 | h29159
                                · linarith only [h22350, h29159, hlam]
                                · rcases p29134_3 (m.d 2 4) (by simp) with h29161 | h29161
                                  · linarith only [h22351, h29161, hlam]
                                  · rcases p29134_3 (m.d 2 5) (by simp) with h29163 | h29163
                                    · linarith only [h29163, hlam, p29134_0]
                                    · rcases h3bigk with h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c | h29165c
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h15532, hlam, p29165_1]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h18443, h28286, h28290, hc23, hc34, hlam, hphi, p29060_1, p29165_1]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h22353, hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h27842, hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h28506, h29059, hc03, hc34, hlam, hphi, p29165_1]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h28506, h29059, hc23, hc34, hlam, hphi, p29165_1]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h28290, hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h28506, hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h22350, hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h28287, hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h28509, hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h28511, hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        rcases p29165_3 (m.d 0 3) (by simp) with h29181 | h29181
                                        · linarith only [h29181, hlam, p29165_0]
                                        · rcases p29165_3 (m.d 1 3) (by simp) with h29183 | h29183
                                          · linarith only [h28290, h29183, hlam]
                                          · linarith only [h15532, h29183, hlam]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h15532, hc01, hc34, hlam, hphi, ht12, ht23, p29165_1]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        rcases p29165_3 (m.d 0 3) (by simp) with h29187 | h29187
                                        · linarith only [h22353, h29187, hlam]
                                        · linarith only [h22350, h29187, hlam]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h15532, h27842, hc01, hc34, hlam, hphi, ht12, ht23, p29165_1]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        rcases p29165_3 (m.d 0 3) (by simp) with h29192 | h29192
                                        · linarith only [h29192, hlam, p29165_0]
                                        · rcases p29165_3 (m.d 1 3) (by simp) with h29194 | h29194
                                          · linarith only [h28506, h29194, hlam]
                                          · linarith only [h15532, h29194, hlam]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h15532, hc01, hc35, hlam, hphi, ht12, ht23, p29165_1]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        rcases p29165_3 (m.d 0 3) (by simp) with h29198 | h29198
                                        · linarith only [h27842, h29198, hlam]
                                        · linarith only [h22350, h29198, hlam]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [h29059, hlam, p29165_0]
                                      · have p29165_0 := h29165c.1
                                        have p29165_1 := h29165c.2.1
                                        have p29165_2 := h29165c.2.2.1
                                        have p29165_3 := h29165c.2.2.2
                                        linarith only [hlam, p29165_0]
                              · linarith only [h28289, h29158, hlam]
                            · linarith only [h29157, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h15532, h22351, h28286, hc01, hc12, hlam, hphi, p29060_1, p29134_1]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            rcases p29134_3 (m.d 0 2) (by simp) with h29207 | h29207
                            · linarith only [h0, h29207, hlam]
                            · linarith only [h22350, h29207, hlam]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            rcases p29134_3 (m.d 0 2) (by simp) with h29210 | h29210
                            · linarith only [h0, h29210, hlam]
                            · linarith only [h22351, h29210, hlam]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            rcases p29134_3 (m.d 0 2) (by simp) with h29213 | h29213
                            · linarith only [h0, h29213, hlam]
                            · linarith only [h22352, h29213, hlam]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h22350, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h28287, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h28509, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h28511, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h22351, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h28288, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h22351, h28286, h28513, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p29134_1]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h28513, hlam, p29134_1]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h22352, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h28289, hlam, p29134_0]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h18443, h28286, h28290, h28513, hc23, hc34, hlam, hphi, p29134_1]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [h18443, h28286, h28290, h28509, h28513, hc23, hc34, hlam, hphi, p29134_1]
                          · have p29134_0 := h29134c.1
                            have p29134_1 := h29134c.2.1
                            have p29134_2 := h29134c.2.2.1
                            have p29134_3 := h29134c.2.2.2
                            linarith only [hlam, p29134_0]
                        · linarith only [h27842, h29133, hlam]
                      · linarith only [h22353, h29132, hlam]
                  · linarith only [h22350, h29129, hlam]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [h28286, hlam, p29060_1]
              · have p29060_0 := h29060c.1
                have p29060_1 := h29060c.2.1
                have p29060_2 := h29060c.2.2.1
                have p29060_3 := h29060c.2.2.2
                linarith only [hlam, p29060_0]
            · linarith only [h18443, h28286, h28290, h29059, hlam]
    · linarith only [h18443, h28286, h28508, hlam]

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28286 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h28287 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h28288 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h28289 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 1 3 4 (by decide) (by decide) with h28290 | h28290
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842 h28286 h28287 h28288 h28289 h28290
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842 h28286 h28287 h28288 h28289 h28290

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28286 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h28287 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h28288 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h28289 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  linarith only [h0, h22352, h28289, hlam]

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28286 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h28287 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h28288 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 1 2 5 (by decide) (by decide) with h28289 | h28289
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842 h28286 h28287 h28288 h28289
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842 h28286 h28287 h28288 h28289

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28286 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h28287 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h28288 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  linarith only [h0, h22351, h28288, hlam]

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28286 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h28287 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 1 2 4 (by decide) (by decide) with h28288 | h28288
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842 h28286 h28287 h28288
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842 h28286 h28287 h28288

end R2N4
