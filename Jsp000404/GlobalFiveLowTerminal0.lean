import Jsp000404.GlobalFiveLowStrongModel

namespace Jsp404.GlobalFiveLowTerminal

set_option maxHeartbeats 32000000 in
theorem model_impossible_0 {n delta : ℝ} (m : FiveModel n delta 0) : False := by
  have hn := m.hn
  obtain ⟨hdelta0, hdelta1⟩ := m.hdelta
  obtain ⟨h010, h011⟩ := m.range 0 1 (by decide)
  obtain ⟨h020, h021⟩ := m.range 0 2 (by decide)
  obtain ⟨h030, h031⟩ := m.range 0 3 (by decide)
  obtain ⟨h040, h041⟩ := m.range 0 4 (by decide)
  obtain ⟨h120, h121⟩ := m.range 1 2 (by decide)
  obtain ⟨h130, h131⟩ := m.range 1 3 (by decide)
  obtain ⟨h140, h141⟩ := m.range 1 4 (by decide)
  obtain ⟨h230, h231⟩ := m.range 2 3 (by decide)
  obtain ⟨h240, h241⟩ := m.range 2 4 (by decide)
  obtain ⟨h340, h341⟩ := m.range 3 4 (by decide)
  have hc10 := m.symm 1 0
  have hc20 := m.symm 2 0
  have hc30 := m.symm 3 0
  have hc40 := m.symm 4 0
  have hc21 := m.symm 2 1
  have hc31 := m.symm 3 1
  have hc41 := m.symm 4 1
  have hc32 := m.symm 3 2
  have hc42 := m.symm 4 2
  have hc43 := m.symm 4 3
  rcases m.triangle 0 1 2 (by decide) (by decide) with ⟨ht012a,ht012b,ht012c,ht012d,ht012e⟩ | ⟨ht012a,ht012b,ht012c,ht012d,ht012e⟩
  ·
    rcases m.triangle 0 1 3 (by decide) (by decide) with ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩ | ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 0 1 3 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht123a, ht234a, hbg2]
                      ·
                        linarith only [hdelta1, h010, ht012a, h341, ht234a, hbg2]
                      ·
                        linarith only [hdelta1, h010, ht012a, h241, ht123a, hbg2]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 2 3 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, h010, h341, ht123a, ht234a, hbg1]
                        ·
                          linarith only [hdelta1, h010, ht012a, h341, ht123c, ht234a, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht013c, ht023b, ht124c, hbg2, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht012b, ht023b, ht134b, hbg1, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht023b, ht234b, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h010, ht012a, h341, ht123a, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht014c, ht034b, ht123a, ht234a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht023b, ht124a, ht134b, hbg2, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht012a, ht023b, ht124a, ht134b, hbg2, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht012a, ht023b, ht124a, ht134b, hbg2, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, ht234b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, ht234b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht123a, ht134b, hbg1, hbg3c]
                        ·
                          linarith only [hdelta1, ht012c, ht124c, ht134b, hbg2, hbg1b]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht124c, hbg2, hbg1b]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, ht123a, ht234b, hbg2, hbg1a, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht023b, ht234b, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h010, h341, ht123a, hbg1a, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, ht123a, ht134b, ht234a, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, ht234b, hbg2, hbg3a, hbg3b]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, ht234b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, ht234b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, ht234b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, ht234b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht123a, ht134b, hbg3c, hbg1c]
                        ·
                          linarith only [hdelta1, ht012c, ht124c, hbg2, hbg1a, hbg1b]
                        ·
                          linarith only [hdelta1, ht012c, ht124c, ht134b, hbg2, hbg1a]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht124c, hbg2, hbg1a]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht234a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, ht012a, h341, ht234c, hbg2c]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 2 3 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, h010, h231, hbg2a, hbg1]
                        ·
                          linarith only [hdelta1, ht012c, ht123c, ht234b, hbg2b, hbg1]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht124c, hbg2b, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht012a, ht023b, ht134b, ht234b, hbg1, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, h010, h341, ht013a, ht234a, hbg3]
                          ·
                            linarith only [hdelta1, h020, h341, ht012c, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht014c, ht034b, ht234a, hbg2a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht013b, ht134b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht134b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht134b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h010, h341, ht013a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht012a, ht014c, ht034b, hbg2a, hbg3c, hbg1]
                        ·
                          linarith only [hdelta1, h010, h341, ht134a, hbg1c]
                        ·
                          linarith only [hdelta1, h010, h341, ht012c, ht123b, ht124c, ht234a, hbg1c, hbg2c]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, ht234b, hbg3, hbg1a, hbg2c]
                          ·
                            linarith only [hdelta1, h010, h231, ht013c, ht023b, ht234b, hbg3, hbg1a, hbg2c]
                          ·
                            linarith only [hdelta1, h010, h341, hbg2a, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, ht014c, ht034b, ht234a, hbg2a, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, ht134b, ht234b, hbg1c, hbg2c, hbg3a]
                          ·
                            linarith only [hdelta1, ht023b, ht134b, ht234b, hbg1c, hbg2c, hbg3a]
                          ·
                            linarith only [hdelta1, ht023b, ht134b, ht234b, hbg1c, hbg2c, hbg3a]
                          ·
                            linarith only [hdelta1, h010, h341, ht013a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht134b, hbg2a, hbg1c, hbg3c]
                        ·
                          linarith only [hdelta1, h010, ht012a, h241, ht124c, hbg1c]
                        ·
                          linarith only [hdelta1, ht012a, ht134b, hbg1c]
                        ·
                          linarith only [hdelta1, ht012a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht023a, hbg2c]
                    ·
                      have hb3 := m.budget 3 (by decide) 0 1 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc31, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht023e, ht134a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, h010, ht012a, h231, ht123b, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht023e, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht134a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht023e, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023e, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, h010, ht012a, h231, ht123b, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht134a, ht234a]
                    ·
                      have hb3 := m.budget 3 (by decide) 0 4 1 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc31, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023e, ht034a, ht123c, hbg3]
                      ·
                        linarith only [hdelta1, ht023e, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht123c, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023e, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht023e, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023e, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht123b, ht124c, ht134b]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht134a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 0 4 1 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht023e, ht034a, ht124a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht123a, ht124a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h030, h231, ht034a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht124a, ht234b, hbg2c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 0 3 1 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h010, h241, ht012b, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht023a, ht124a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht023a, ht123a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht124a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2c]
                    ·
                      linarith only [ht123b, ht134a, ht234a]
                  ·
                    linarith only [ht123c, ht124b, ht134c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 0 3 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, hbg2c]
                    ·
                      linarith only [ht123b, ht134a, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 0 3 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, ht123c, ht134a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123c, ht134a, ht234a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht123c, ht134a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht123c, ht134a, ht234a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123c, ht134a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, hbg2c]
                    ·
                      have hb2 := m.budget 2 (by decide) 0 4 3 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012e, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht023b, ht034a, ht234a, hbg2]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht123a, ht234a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c, ht234c]
                      ·
                        linarith only [hdelta1, ht123a, hbg2c, ht234c]
                      ·
                        linarith only [hdelta1, h010, h121, ht012b, ht023b, ht034a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, hbg2c]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013c, ht034a, ht123c, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 0 1 4 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht124a, ht234d, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht034a, ht123c, ht124a, ht234d, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht013c, ht034a, ht124a, ht234d, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht034a, ht123a, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123c, ht124a, ht234d, hbg3c, hbg2]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123b, hbg3b, hbg2]
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht124a, ht234c, hbg2, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123b, hbg3b, hbg2]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht034a, ht124a, ht234c, hbg3c, hbg2]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123b, hbg3a, hbg2]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht012a, ht013d, ht234d, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, h010, ht012a, h231, ht034a, ht123c, ht234d, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, h010, ht012a, h231, ht013c, ht034a, ht234d, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, ht012a, ht013d, ht034a, ht234c, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, h010, ht012a, h231, ht123c, ht234d, hbg2, hbg3c]
                        ·
                          linarith only [hdelta1, h010, ht012a, h231, ht013c, ht234d, hbg2, hbg3c]
                        ·
                          linarith only [hdelta1, ht012a, ht013d, ht234c, hbg2, hbg3c]
                        ·
                          linarith only [hdelta1, ht023e, hbg3c]
                        ·
                          linarith only [hdelta1, ht034a, ht123c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, h010, ht012a, h231, ht124a, hbg2]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013d, ht124a, ht234d, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, h010, h131, ht034a, ht124a, ht234d, hbg3, hbg1]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht024b, ht034c, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, ht013d, ht034a, ht124a, ht234c, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, ht124a, ht234c, hbg3b, hbg2, hbg1]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, ht034c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht013d, ht124a, ht234c, hbg3c, hbg1]
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, ht124a, ht234c, hbg3a, hbg2, hbg1]
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, ht124a, ht234c, hbg3a, hbg2, hbg1]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, ht034c, hbg3a, hbg2]
                        ·
                          linarith only [hn, hdelta1, ht012c, ht123c, ht134c, hbg2, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht014c, ht024b, ht123c, hbg2, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht124a, ht234d, hbg3, hbg1]
                          ·
                            linarith only [hn, hdelta1, ht013b, hbg3, hbg1]
                          ·
                            linarith only [hn, hdelta1, ht012c, ht124b, ht134c, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht034a, ht123a, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht013b, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht124b, ht134c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht124a, ht234c, hbg3c, hbg1]
                          ·
                            linarith only [hdelta1, ht013b, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht013b, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht124b, ht134c, hbg3a, hbg2]
                        ·
                          linarith only [hdelta1, ht012c, ht123c, ht134c, hbg2, hbg1b]
                        ·
                          linarith only [hdelta1, ht014c, ht024b, ht123c, hbg2, hbg1b]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013c, ht124a, ht234d, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, hbg3, hbg1b]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht024b, ht034c, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht034a, ht124a, ht234c, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, ht013c, ht124a, ht234c, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht023b, hbg2, hbg3a, hbg3b]
                          ·
                            linarith only [hdelta1, ht024b, ht034c, ht123c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, ht034c, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, ht012c, ht123c, hbg1a, hbg2, hbg1b]
                        ·
                          linarith only [hdelta1, ht012c, ht123c, ht134c, hbg1a, hbg2]
                        ·
                          linarith only [hdelta1, ht014c, ht024b, ht123c, hbg1a, hbg2]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht234d, hbg3, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht034a, ht234d, hbg3, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht013c, ht034a, ht234d, hbg3, hbg2c]
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht034a, ht234c, hbg3, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123c, ht234d, hbg3c, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht013c, ht234d, hbg3c, hbg2c]
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht234c, hbg3c, hbg2c]
                        ·
                          linarith only [hdelta1, ht023e, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht034a, ht234c, hbg3c, hbg2c]
                        ·
                          linarith only [hdelta1, ht013c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, ht012a, h231, hbg2c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h010, h241, hbg2a, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht124c, ht234c, hbg1, hbg2b]
                          ·
                            linarith only [hdelta1, ht014c, ht024b, ht123c, hbg1, hbg2b]
                          ·
                            linarith only [hdelta1, ht012a, h231, h340, ht013c, ht234c, hbg2a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht013d, ht124c, ht234d, hbg1c, hbg3]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 0 1 2 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc40, hc41, hc42] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h010, h131, h241, h340, ht014c, hbg1c, hbg4, hbg2a]
                            ·
                              linarith only [hdelta1, h040, h131, hbg4, hbg1b]
                            ·
                              linarith only [hdelta1, ht013d, ht124b, ht234d, hbg4, hbg1a, hbg3]
                            ·
                              linarith only [hdelta1, ht013d, hbg4, hbg1a, hbg2a, hbg3]
                            ·
                              linarith only [hdelta1, ht013d, ht024b, ht123c, ht234d, hbg1c, hbg2c, hbg3, hbg4b]
                            ·
                              linarith only [hdelta1, ht014c, ht234d, hbg4c]
                            ·
                              linarith only [hdelta1, ht012c, ht013c, ht123c, hbg2c, hbg3, hbg4b]
                            ·
                              linarith only [hdelta1, h010, h241, ht024b, ht123c, hbg1c, hbg2c, hbg4a]
                            ·
                              linarith only [hdelta1, h010, h241, ht024b, ht123c, hbg1c, hbg2c, hbg4a]
                            ·
                              linarith only [hdelta1, ht012c, ht013d, ht123c, ht124b, hbg1c, hbg2c, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, h241, h340, ht013c, hbg1c, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht123c, hbg1c, hbg2b]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht124c, ht234d, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht124b, hbg1c]
                        ·
                          linarith only [hdelta1, ht023b, ht123c, hbg3, hbg2b]
                        ·
                          linarith only [hdelta1, ht013c, ht024b, ht034c, hbg3, hbg2b]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h010, h231, ht234c, hbg1, hbg2a]
                          ·
                            linarith only [hdelta1, ht012c, ht124c, ht234c, hbg1, hbg2b]
                          ·
                            linarith only [hdelta1, ht013d, ht014a, ht034a, ht123c, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht034a, ht234c, hbg1, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, ht013d, ht034a, ht124c, ht234c, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht014c, ht034b, ht123c, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, ht034a, ht123a, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht014c, ht034b, ht123c, hbg1b, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht034a, ht124c, ht234c, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht014c, ht034b, ht123c, hbg1a, hbg3]
                        ·
                          linarith only [hdelta1, ht012c, ht123c, ht234d, hbg2c, hbg3c]
                        ·
                          linarith only [hdelta1, ht012c, ht013c, ht234d, hbg2c, hbg3c]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 2 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h010, h231, ht234c, hbg2a, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht013d, ht124c, ht234c, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, ht013d, ht014a, ht123c, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht123a, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, ht013d, ht124c, ht234c, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht013d, ht123c, ht124b, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht234c, hbg2a, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, h010, ht012a, h231, ht123c, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht124c, ht234c, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht014a, hbg1c]
                        ·
                          linarith only [hdelta1, h231, h340, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht034a, ht123c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012c, ht124a, hbg2c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 0 4 1 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht124a, hbg2c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht023c, ht034a, ht123b, ht134a]
                  ·
                    linarith only [ht123c, ht124b, ht134c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 0 4 3 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012e, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c, ht234c]
                      ·
                        linarith only [hdelta1, ht123a, hbg2c, ht234c]
                      ·
                        linarith only [hdelta1, ht012e, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, hbg2c]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht023b, ht024c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 0 1 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012c, ht123a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht012c, ht024a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht123a, ht234e, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht234e, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h231, h340, ht024a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht024a, hbg2c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023a, ht024c, ht034b, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 0 3 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht123a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht024a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, h121, h340, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 0 1 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012c, ht124a, ht234d, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, ht234d, hbg2]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, ht234d, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht124a, ht234d, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht234d, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h230, h341, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, hbg2c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht123c, ht124b, ht134c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 0 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h121, h230, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h121, h230, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h121, h230, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                    ·
                      linarith only [ht013c, ht023b, ht134a, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 0 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h121, h230, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123d, ht134a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, h121, h230, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123c, ht134a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, ht123d, ht134a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123c, ht134a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123c, ht134a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
            ·
              linarith only [ht023c, ht024b, ht034c]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 0 3 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc20, hc21] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht024a, ht123d, hbg2, hbg1]
                        ·
                          linarith only [hdelta1, ht012d, ht134a, hbg2, ht234e, hbg1]
                        ·
                          linarith only [hdelta1, h010, h121, ht024a, ht134a, hbg2, ht234e, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht012c, ht023c, hbg2, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht023b, ht123c, hbg2, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h341, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht012d, ht024a, ht134a, ht234b, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, h010, h341, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, h010, h341, hbg3a, hbg1]
                        ·
                          linarith only [hdelta1, h230, h341, ht012d, ht134a, hbg2c, hbg1]
                        ·
                          linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, ht012c, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h121, ht134a, hbg2c, ht234e, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht013c, ht134a, hbg2c, ht234e, hbg3]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, hbg2b, hbg3]
                          ·
                            linarith only [hdelta1, h010, h341, ht012c, ht234b, hbg2b, hbg3, hbg1, hbg2a]
                          ·
                            linarith only [hdelta1, h010, h021, ht134a, ht234b, hbg3, hbg1, hbg2a]
                          ·
                            linarith only [hdelta1, h230, h341, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht013c, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht023b, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, hbg3a, hbg1]
                        ·
                          linarith only [hdelta1, ht024a, ht234b, hbg2c]
                      ·
                        have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc20, hc21] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, h141, h230, ht012d, ht013a, ht024a, hbg2, hbg1]
                        ·
                          linarith only [hdelta1, ht012d, ht013a, ht124d, hbg2, hbg1]
                        ·
                          linarith only [hdelta1, h010, h121, ht013a, ht024a, ht124d, hbg2, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht013c, ht023b, ht124c, hbg2, hbg1]
                        ·
                          linarith only [hdelta1, h121, h230, ht012d, ht013a, ht124c, hbg1, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht124c, hbg2b, hbg1]
                        ·
                          linarith only [hdelta1, h010, h121, ht013a, ht134c, ht234e, hbg1, hbg2c]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht124c, hbg2b, hbg1]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht124c, hbg2b, hbg1]
                      ·
                        have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc20, hc21] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, h121, h230, ht012d, ht014a, ht024a, hbg2, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h121, h230, ht013c, ht134b, hbg3, hbg1]
                          ·
                            linarith only [hn, hdelta1, h030, h121, ht134b, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht012d, ht013a, hbg2, ht234e, hbg3]
                          ·
                            linarith only [hdelta1, ht012d, ht013a, ht134a, ht234b, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h030, h121, ht134b, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, h121, h230, ht013c, ht134b, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h121, h230, ht013c, ht134b, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h030, h121, ht134b, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h030, h121, ht134b, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht012d, ht013a, ht234b, hbg2, hbg3c]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h121, h230, ht023c, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h010, h121, ht013b, ht024a, ht134a, hbg2, hbg3, ht234e]
                          ·
                            linarith only [hdelta1, h010, h121, ht013a, ht024a, hbg2, hbg3, ht234e]
                          ·
                            linarith only [hdelta1, h010, h121, ht013a, ht023a, ht134a, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h121, h230, ht023c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, h121, h230, ht023c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, h121, h230, ht023c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, h030, h121, ht134b, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h030, h121, ht134b, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h010, h121, ht013a, ht024a, ht234b, hbg3c, hbg2]
                        ·
                          linarith only [hdelta1, ht012d, ht014a, ht024a, ht234b, hbg2, hbg1]
                        ·
                          linarith only [hdelta1, h121, h230, ht014c, ht024b, hbg1, hbg2a]
                        ·
                          linarith only [hdelta1, h121, h230, ht014c, ht024b, hbg1, hbg2a]
                        ·
                          linarith only [hdelta1, h121, h230, ht014c, ht024b, hbg1, hbg2a]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h121, h230, ht023c, hbg2b, hbg3]
                          ·
                            linarith only [hdelta1, h030, h121, ht134a, hbg2c, ht234e, hbg3]
                          ·
                            linarith only [hdelta1, h010, h121, ht013a, hbg2c, ht234e, hbg3]
                          ·
                            linarith only [hdelta1, h010, h121, ht013a, ht134a, ht234b, hbg2c, hbg3]
                          ·
                            linarith only [hdelta1, h121, h230, ht014c, ht034b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h121, h230, ht014c, ht034b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h121, h230, ht014c, ht034b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h030, h121, ht134b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h030, h121, ht134b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h010, h121, ht013a, ht234b, hbg2c, hbg3c]
                        ·
                          linarith only [hdelta1, ht014c, ht024b, ht234b, hbg2b, hbg1]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht134b, hbg2b, hbg1]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc40, hc41, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht012c, ht013a, ht024c, ht134a, ht234e, hbg4, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht014b, ht124c, hbg4, hbg1]
                        ·
                          linarith only [hdelta1, ht012c, ht014a, ht024a, ht234e, hbg4, hbg1]
                        ·
                          linarith only [hdelta1, ht012c, ht013a, ht024a, ht134a, hbg4, hbg1]
                        ·
                          linarith only [hdelta1, ht014b, ht124c, hbg4b, hbg1]
                        ·
                          linarith only [hdelta1, ht014c, ht234e, hbg4c]
                        ·
                          linarith only [hdelta1, ht012c, ht013a, ht024c, ht134a, hbg1, hbg4c]
                        ·
                          linarith only [hdelta1, ht013b, ht034b, ht124c, hbg4a, hbg1]
                        ·
                          linarith only [hdelta1, ht013b, ht034b, ht124c, hbg4a, hbg1]
                        ·
                          linarith only [hdelta1, ht012c, ht013a, ht024a, ht134b, hbg4c, hbg1]
                      ·
                        have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc20, hc21] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, h121, h230, ht012d, ht024a, ht124c, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, ht012d, ht124d, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, h010, h121, ht024a, ht134c, hbg1c, ht234e, hbg2]
                        ·
                          linarith only [hdelta1, ht012d, ht023a, ht124c, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, h121, h230, ht012d, ht124c, hbg1c, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h021, ht024a, ht124c, hbg1c, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h121, ht134c, hbg1c, ht234e, hbg2c]
                        ·
                          linarith only [hdelta1, ht012d, ht124c, ht234b, hbg1c, hbg2c]
                        ·
                          linarith only [hdelta1, ht023a, hbg2c]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc40, hc41, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h121, h230, ht014c, ht234b, hbg1b, hbg4]
                        ·
                          linarith only [hdelta1, h040, h121, hbg1b, hbg4]
                        ·
                          linarith only [hdelta1, h010, h341, ht134b, hbg1a, hbg4]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h121, h230, ht014c, ht024b, hbg1b, hbg2]
                          ·
                            linarith only [hdelta1, ht012d, ht134a, hbg2, hbg1a, hbg4]
                          ·
                            linarith only [hdelta1, h010, h121, ht024a, ht134a, hbg2, hbg1a, hbg4]
                          ·
                            linarith only [hdelta1, ht013c, ht014c, ht023b, ht024b, ht134a, hbg1b, hbg2, hbg4]
                          ·
                            linarith only [hdelta1, h121, h230, ht012d, ht134b, hbg2c, hbg1c]
                          ·
                            linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, h010, h021, ht024a, ht134b, hbg2c, hbg1c]
                          ·
                            linarith only [hdelta1, h010, h121, ht134a, hbg2c, hbg1a, hbg4]
                          ·
                            linarith only [hdelta1, ht012d, ht134b, ht234b, hbg2c, hbg1c]
                          ·
                            linarith only [hdelta1, ht024a, ht234b, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h230, ht234b, hbg1b, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, hbg4c, ht234e]
                        ·
                          linarith only [hdelta1, h010, h121, ht014c, ht134a, hbg4c, hbg1c]
                        ·
                          linarith only [hdelta1, ht034e, hbg4c]
                        ·
                          linarith only [hdelta1, h010, h121, ht024b, ht134a, hbg4c, hbg1c]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h230, h341, ht014c, ht024b, hbg2, hbg4a]
                          ·
                            linarith only [hdelta1, ht012d, ht134b, hbg4c, hbg2, hbg1a]
                          ·
                            linarith only [hdelta1, h010, h121, ht024a, ht134b, hbg4c, hbg2, hbg1a]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, ht134b, hbg1b, hbg2]
                          ·
                            linarith only [hdelta1, h121, h230, ht012d, ht134b, hbg1c, hbg2c]
                          ·
                            linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, h010, h021, ht024a, ht134b, hbg1c, hbg2c]
                          ·
                            linarith only [hdelta1, h010, h121, ht134b, hbg4c, hbg1a, hbg2c]
                          ·
                            linarith only [hdelta1, ht012d, ht134b, ht234b, hbg1c, hbg2c]
                          ·
                            linarith only [hdelta1, ht023a, hbg2c]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc40, hc41, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht012c, ht024c, ht134a, hbg1c, ht234e, hbg4]
                        ·
                          linarith only [hdelta1, ht013b, ht034b, ht124c, hbg1b, hbg4]
                        ·
                          linarith only [hdelta1, h010, h341, ht134b, hbg1a, hbg4]
                        ·
                          linarith only [hdelta1, ht012c, ht024a, ht134a, hbg1c, hbg4]
                        ·
                          linarith only [hdelta1, h230, h341, ht134a, ht124c, ht234b, hbg1c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, ht234e, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, ht134a, ht124c, hbg1c, hbg4c]
                        ·
                          linarith only [hdelta1, ht034e, hbg4c]
                        ·
                          linarith only [hdelta1, ht024b, ht134a, ht124c, hbg1c, hbg4c]
                        ·
                          linarith only [hdelta1, ht012c, ht024a, ht134b, hbg1c, hbg4c]
                      ·
                        linarith only [hdelta1, h010, h121, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, hbg1c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 0 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc30, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht034a, ht123d, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht013e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht123d, hbg3]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht123d, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123d, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013e, hbg3c]
                      ·
                        linarith only [hdelta1, ht023b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, hbg3c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 4 0 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc30, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013c, ht034a, ht123d, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht123d, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht123d, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht034a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht123d, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123d, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123d, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht234a, hbg3c]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 3 0 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht023a, ht124d, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, h121, h240, ht012d, ht014a, ht023a, ht123c, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, h121, h340, ht012d, ht013a, ht023a, ht234b, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, ht012c, ht014a, ht023a, ht124d, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, h121, h340, ht012d, ht023a, ht123c, ht234b, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, h121, h340, ht013c, ht023b, ht234b, hbg1b, hbg2]
                        ·
                          linarith only [hdelta1, ht012c, ht023a, ht124d, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, h121, h340, ht013c, ht023b, ht234b, hbg1b, hbg2]
                        ·
                          linarith only [hdelta1, h131, h340, ht012c, ht014a, ht023a, ht234b, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, h121, h340, ht013c, ht023b, ht234b, hbg1a, hbg2]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht134d, ht234a, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, ht012d, ht014a, ht123d, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, h121, h340, ht012d, ht013a, ht234a, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, ht012c, ht014a, ht134d, ht234a, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, h121, h340, ht012d, ht123c, ht234a, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, h121, h340, ht012d, ht234a, ht134c, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, ht012c, ht134d, ht234a, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, h010, h121, ht014a, hbg1c]
                        ·
                          linarith only [hdelta1, h131, h340, ht012c, ht014a, ht234a, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht234a, hbg2]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht023a, ht134d, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012d, ht023c, ht134d, ht234a, hbg1, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht023b, ht123c, ht234c, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, ht012d, ht023a, ht234a, ht134c, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht234c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht024b, ht034c, ht123c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht012d, ht023a, ht134c, hbg3c, hbg1]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht234c, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht234c, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, ht234c, hbg3a, hbg2]
                        ·
                          linarith only [hn, hdelta1, ht014c, ht024b, ht123c, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, ht012d, ht013a, ht023a, ht234c, hbg1, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht014a, ht023a, ht134d, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, ht014a, ht123c, ht134d, ht234a, hbg1, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht013b, ht123c, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht013a, ht023a, ht234a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht234c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht013b, ht123c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht012c, ht014a, ht023a, ht134c, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht123c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht013c, ht123c, ht234c, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht013b, ht123c, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, ht014c, ht024b, ht123c, hbg1b, hbg2]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht234c, hbg1b, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht023a, ht134d, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht134d, ht234a, ht234c, hbg3, hbg1a, hbg1b, hbg2]
                          ·
                            linarith only [hn, hdelta1, ht023b, ht123c, ht234c, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, ht023a, ht234a, ht134c, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht234c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht024b, ht034c, ht123c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, ht023a, ht134c, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht024b, ht034c, ht123c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht123c, ht234c, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, ht234c, hbg3a, hbg2]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht234c, hbg1b, hbg2]
                        ·
                          linarith only [hdelta1, ht014c, ht024b, ht123c, hbg1a, hbg2]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht234c, hbg1a, hbg2]
                      ·
                        have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht012d, ht124d, hbg1, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h240, ht012d, ht014a, ht123c, hbg1, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h340, ht012d, ht013a, ht234b, hbg1, hbg2c]
                        ·
                          linarith only [hdelta1, ht012c, ht014a, ht124d, hbg1, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h340, ht012d, ht123c, ht234b, hbg2c, hbg1c]
                        ·
                          linarith only [hdelta1, h121, h340, ht012d, ht234b, ht134c, hbg2c, hbg1c]
                        ·
                          linarith only [hdelta1, ht012c, ht124d, hbg2c, hbg1c]
                        ·
                          linarith only [hdelta1, h121, h340, ht012d, ht014a, ht234b, hbg2c, hbg1c]
                        ·
                          linarith only [hdelta1, h131, h340, ht012c, ht014a, ht234b, hbg2c, hbg1c]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h340, ht234a, hbg2c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc42, hc40, hc41] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h121, h340, ht012c, ht234c, hbg2a, hbg4]
                        ·
                          linarith only [hdelta1, ht012c, ht024c, hbg2b, hbg4]
                        ·
                          linarith only [hdelta1, ht024b, ht124c, hbg2b, hbg4]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht234a, hbg1, hbg2a, hbg4]
                          ·
                            linarith only [hdelta1, ht014c, ht024b, ht123c, hbg1, hbg2b]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, ht034c, hbg1, hbg2b]
                          ·
                            linarith only [hdelta1, ht012c, ht014a, ht234a, hbg1, hbg2a, hbg4]
                          ·
                            linarith only [hdelta1, ht012d, ht123c, ht234c, hbg2c, hbg1c]
                          ·
                            linarith only [hdelta1, ht012d, ht134c, ht234c, hbg2c, hbg1c]
                          ·
                            linarith only [hdelta1, ht012c, ht234a, hbg2a, hbg1c, hbg4]
                          ·
                            linarith only [hdelta1, ht012d, ht014a, ht234c, hbg2c, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, ht123c, hbg1c]
                          ·
                            linarith only [hdelta1, ht013a, hbg1c]
                        ·
                          linarith only [hdelta1, ht034d, hbg4c]
                        ·
                          linarith only [hdelta1, ht024b, ht134d, hbg4c]
                        ·
                          have hb1 := m.budget 1 (by decide) 0 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht234c, hbg4c, hbg1, hbg2a]
                          ·
                            linarith only [hdelta1, h121, h340, ht014c, ht024b, ht123c, hbg4a, hbg1]
                          ·
                            linarith only [hdelta1, ht012d, ht013a, ht234c, hbg1, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht014a, ht234c, hbg4c, hbg1, hbg2a]
                          ·
                            linarith only [hdelta1, ht012d, ht123c, ht234c, hbg1c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012d, ht134c, ht234c, hbg1c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht234c, hbg1c, hbg4c, hbg2a]
                          ·
                            linarith only [hdelta1, ht012d, ht014a, ht234c, hbg1c, hbg2c]
                          ·
                            linarith only [hdelta1, ht014a, ht123c, hbg1c]
                          ·
                            linarith only [hdelta1, ht013a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012c, ht123d, ht134c, hbg4c, hbg2c]
                        ·
                          linarith only [hdelta1, ht012c, ht014c, ht234a, hbg4c, hbg2c]
                        ·
                          linarith only [hdelta1, ht012c, ht024b, ht234a, hbg4c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht234c, hbg2c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            linarith only [ht012b, ht014c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht012b, ht014c, ht023b, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013a, ht014c, ht034b, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht012a, ht014a, ht123a, ht134b, ht234a]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 0 2 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h140, ht012a, h231, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123a, ht124b, ht234e, hbg1]
                      ·
                        linarith only [hdelta1, h131, h140, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht123a, ht124b, ht234e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht123c, ht124b, ht234e, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, h231, h340, ht014a, ht123c, ht124b, ht234b, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht023c, ht123b, ht134a, ht034a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht012b, ht014a, ht023a, ht234a, ht134b]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 0 3 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht123a, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht012b, ht014a, ht023a, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, ht123c, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht123b, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h340, ht014a, ht234b, hbg1c, ht124b]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012b, ht014a, ht023a, ht123b, hbg1c]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            linarith only [ht013b, ht014c, ht023c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht013b, ht014c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012a, ht014c, ht124a, ht024b]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 4 0 3 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht123c, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123d, ht134b, ht234a, hbg1]
                      ·
                        linarith only [hdelta1, h121, h230, ht013a, ht014a, ht134b, ht234a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht123d, ht134b, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h230, ht013a, ht134b, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h230, ht014a, ht134b, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 0 3 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht123c, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht123c, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h340, ht014a, ht124b, ht234b, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          linarith only [ht012b, ht013c, ht023b]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 0 2 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, h230, h241, ht123b, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123b, ht124a, ht234d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, ht123b, ht124c, ht234d, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht123b, ht124a, ht234d, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht123b, ht124c, ht234d, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h230, h341, ht013a, ht123b, ht124c, ht234c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht012b, ht013a, ht034c, ht024b, ht134a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 0 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h121, h230, ht012b, ht024a, ht123b, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123e, ht124c, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht024a, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht123e, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h130, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht024a, ht124b, hbg1c]
                    ·
                      linarith only [ht013b, ht034a, ht123b, ht234a]
                  ·
                    linarith only [ht012b, ht013a, ht034c, ht024b, ht134a]
            ·
              linarith only [ht012b, ht013c, ht034c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 0 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123e, ht124c, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht123e, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h230, ht013a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
                    ·
                      linarith only [ht013b, ht034a, ht123b, ht234a]
                  ·
                    linarith only [ht013a, ht014b, ht034c, ht134a]
            ·
              linarith only [ht013c, ht014b, ht034c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          linarith only [ht012b, ht013c, ht023b]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            linarith only [ht012b, ht014c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012a, ht014c, ht024b, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 4 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1, ht134b]
                      ·
                        linarith only [hdelta1, ht012a, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c, ht134b]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 4 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht124e, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht013c, ht034a, ht134a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht013c, ht034a, ht123e, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013c, ht034a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134b, hbg1c]
                      ·
                        linarith only [hdelta1, ht013c, ht034a, ht134a, hbg1c]
                    ·
                      linarith only [ht123b, ht134a, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 4 3 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h121, h140, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht123e, hbg1]
                      ·
                        linarith only [hdelta1, h121, h230, ht013a, ht134a, ht234a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, h121, ht012a, h230, ht134b, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, h121, h230, ht013a, ht134b, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht134c, hbg1c]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 3 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h121, h140, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, h121, ht012a, h340, ht123b, ht234a, hbg1]
                      ·
                        linarith only [hdelta1, h121, h340, ht013a, ht123b, ht234a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht123e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht134c, hbg1c]
  ·
    rcases m.triangle 0 1 3 (by decide) (by decide) with ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩ | ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 2 0 3 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, h120, h341, ht012a, ht123c, ht234a, hbg1]
                      ·
                        linarith only [hdelta1, h120, h241, ht012a, ht013a, ht124c, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, h120, h341, ht123c, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h120, h341, ht012a, ht124c, ht234c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 0 3 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h120, h341, ht013a, ht134a, hbg1]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht134a, ht234a, hbg1]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht013a, ht234a, ht134c, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, h120, h231, ht134a, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, h120, h231, ht013a, ht234a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h010, h231, ht234a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht234a, ht134a]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 0 4 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht123d, ht134c, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht134a, ht034a, hbg1]
                      ·
                        linarith only [hdelta1, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013b, ht123d, ht034a, ht134b, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, h120, h131, ht012a, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht034a, ht134b, hbg1c]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013c, ht034a, ht123c, ht234a]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 0 4 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht123d, ht134c, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht123d, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht134c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1c]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
          ·
            linarith only [ht012c, ht014b, ht024c]
        ·
          linarith only [ht012c, ht013b, ht023c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht013b, ht014c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013a, ht014a, ht123c, ht234a, ht134b]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 4 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123d, ht124b, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht124b, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, ht123d, ht124b, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht012c, ht013b, ht024c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht012c, ht013a, ht024a, ht123c, ht134b, ht124c, ht234a]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 4 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123d, ht124b, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht123d, hbg1]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht024a, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht024a, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht123d, ht124b, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht024a, ht124a, hbg1c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht012a, ht013a, ht123c, ht124c, ht134b, ht234a]
                    ·
                      have hb1 := m.budget 1 (by decide) 4 2 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h131, h140, ht012a, ht013a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123c, ht234e, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht123c, ht234e, ht124a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123c, ht124b, ht234e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht123c, ht124b, ht234e, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg1c]
                      ·
                        linarith only [hdelta1, ht123d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht124c, hbg1c]
              ·
                linarith only [ht012b, ht023a, ht123a]
        ·
          linarith only [ht012c, ht013b, ht023c]
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 2 3 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h120, h141, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, ht124d, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht124d, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123b, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, ht123b, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 3 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h120, h141, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, h130, h231, ht014a, ht134c, ht234a, hbg1]
                      ·
                        linarith only [hdelta1, ht013a, ht123e, ht134c, ht234a, hbg1]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, h120, h231, ht014a, ht134c, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, h120, h231, ht013a, ht134c, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h130, h231, ht134c, ht234a, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, hbg1c]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
            ·
              linarith only [ht013c, ht014b, ht034c]
          ·
            linarith only [ht013c, ht014b, ht023b, ht024c]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 2 3 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h120, h141, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, ht124d, hbg1]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, ht124d, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, ht012c, ht014a, ht023a, ht123a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht013a, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht014a, ht023a, hbg1c, ht123c]
                      ·
                        linarith only [hdelta1, ht123b, ht124d, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, hbg1c]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, ht123a, hbg1c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht012c, ht014b, ht023a, ht034c, ht134a, ht123c]
                ·
                  linarith only [ht023a, ht024a, ht124a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb1 := m.budget 1 (by decide) 3 2 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        linarith only [hdelta1, h141, h230, ht012a, ht014a, ht123b, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123a, hbg1, ht234d, ht124c]
                      ·
                        linarith only [hdelta1, ht012a, ht123a, hbg1, ht234d, ht124c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, hbg1]
                      ·
                        linarith only [hdelta1, ht014a, ht123b, ht234d, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht123b, ht234d, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, hbg1c]
                      ·
                        linarith only [hdelta1, h230, h341, ht234c, ht123a, ht124c, hbg1c]
                      ·
                        linarith only [hdelta1, ht014a, ht123c, hbg1c]
                      ·
                        linarith only [hdelta1, ht012a, ht123c, hbg1c]
                    ·
                      linarith only [ht012c, ht014a, ht023a, ht134c, ht234a]
                  ·
                    linarith only [ht013a, ht014b, ht034c, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
            ·
              linarith only [ht012c, ht014b, ht023c, ht034c]
          ·
            linarith only [ht012c, ht014b, ht024c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 1 0 3 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h120, h341, ht023a, hbg2, ht234a]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, h120, h341, ht012e, ht014a, ht134b, hbg2, hbg1, ht234a]
                        ·
                          linarith only [hdelta1, h130, h341, ht012e, ht014a, hbg2, hbg1, ht234a]
                        ·
                          linarith only [hdelta1, ht012e, hbg2, hbg1, ht234a, ht134e]
                        ·
                          linarith only [hdelta1, ht012b, ht014a, hbg2, hbg1, ht234a, ht134e]
                        ·
                          linarith only [hdelta1, h120, h341, ht012e, ht014a, hbg2, ht234a, hbg1c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012e, ht134b, hbg2, ht234a, hbg1c]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012e, ht123b, hbg2, ht234a, hbg1c]
                        ·
                          linarith only [hdelta1, ht014a, ht123b, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, hbg2, ht234a, ht134e, hbg1c]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, h120, h241, ht012e, ht013a, ht023a, hbg2, hbg1]
                        ·
                          linarith only [hdelta1, h130, h341, ht012e, ht014a, ht023a, hbg2, hbg1, ht234c]
                        ·
                          linarith only [hdelta1, ht012e, ht023a, hbg2, ht124e, hbg1]
                        ·
                          linarith only [hdelta1, ht012b, ht014a, ht023a, hbg2, hbg1, ht234c, ht134e]
                        ·
                          linarith only [hdelta1, h120, h341, ht013b, ht023c, hbg2, ht234c, hbg1a]
                        ·
                          linarith only [hdelta1, h120, h341, ht013b, ht023c, hbg2, ht234c, hbg1a]
                        ·
                          linarith only [hdelta1, h120, h341, ht013b, ht023c, hbg2, ht234c, hbg1a]
                        ·
                          linarith only [hdelta1, h120, h241, ht012e, ht023a, ht123b, hbg2, hbg1c]
                        ·
                          linarith only [hdelta1, ht014a, ht123b, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht023a, hbg2, ht124e, hbg1c]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hn, hdelta1, ht013b, ht023c, hbg2, ht234b, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht014b, ht123b, hbg2, ht024c, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht023c, ht123b, hbg2, ht234b, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht013b, ht123b, hbg2, ht234b, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, hbg3, hbg1, ht134e]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, ht134b, hbg3, hbg1, ht234a]
                          ·
                            linarith only [hdelta1, ht034b, ht123b, hbg2, ht024c, hbg3a]
                          ·
                            linarith only [hdelta1, ht034b, ht123b, hbg2, ht024c, hbg3a]
                          ·
                            linarith only [hdelta1, ht034b, ht123b, hbg2, ht024c, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht123b, hbg2, ht234b, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht123b, hbg2, ht234b, hbg3a]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, ht134b, hbg1, hbg3c]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht013c, ht123b, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht013b, ht014a, ht123b, hbg3, hbg1, ht234a, ht134e]
                          ·
                            linarith only [hdelta1, ht012b, ht014a, ht023a, hbg3, hbg1, ht134e]
                          ·
                            linarith only [hdelta1, ht012b, ht013a, ht023a, hbg3, hbg1, ht234a]
                          ·
                            linarith only [hdelta1, ht014c, ht034b, ht123b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht014c, ht034b, ht123b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht014c, ht034b, ht123b, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht123b, hbg2, ht234b, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht123b, hbg2, ht234b, hbg3a]
                          ·
                            linarith only [hdelta1, ht012b, ht014a, ht023a, ht134b, hbg1, hbg3c]
                        ·
                          linarith only [hdelta1, ht014b, hbg2, ht024c, hbg1b, hbg1a]
                        ·
                          linarith only [hdelta1, ht013b, ht034b, hbg2, ht024c, hbg1a]
                        ·
                          linarith only [hdelta1, ht013b, ht034b, hbg2, ht024c, hbg1a]
                        ·
                          linarith only [hdelta1, ht014b, ht123b, hbg2, ht024c, hbg1a]
                        ·
                          linarith only [hdelta1, ht014b, ht123b, hbg2, ht024c, hbg1a]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013c, ht123b, hbg3, hbg1b]
                          ·
                            linarith only [hdelta1, ht013b, ht123b, hbg3, ht234a, hbg1c, ht134e]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, hbg3, hbg1c, ht134e]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, ht134b, hbg3, ht234a, hbg1c]
                          ·
                            linarith only [hdelta1, ht034b, ht123b, hbg2, ht024c, hbg3a]
                          ·
                            linarith only [hdelta1, ht034b, ht123b, hbg2, ht024c, hbg3a]
                          ·
                            linarith only [hdelta1, ht034b, ht123b, hbg2, ht024c, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht123b, hbg2, ht234b, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht123b, hbg2, ht234b, hbg3a]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, ht134b, hbg1c, hbg3c]
                      ·
                        linarith only [hdelta1, h120, h341, ht234a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h341, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, hbg2c]
                      ·
                        have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, h120, h241, ht012e, ht013a, hbg2c, hbg1]
                        ·
                          linarith only [hdelta1, h130, h341, ht012e, ht014a, ht234c, hbg2c, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht124e, hbg2c, hbg1]
                        ·
                          linarith only [hdelta1, ht012b, ht014a, ht234c, hbg2c, ht134e, hbg1]
                        ·
                          linarith only [hdelta1, h120, h341, ht012e, ht014a, hbg1c, ht234c, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012e, ht134b, hbg1c, ht234c, hbg2c]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c]
                        ·
                          linarith only [hdelta1, h130, h341, ht012e, hbg1c, ht234c, hbg2c]
                        ·
                          linarith only [hdelta1, ht014a, ht123b, hbg1c]
                        ·
                          linarith only [hdelta1, ht012b, ht124e, hbg1c, hbg2c]
                      ·
                        have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc41, hc40, hc42, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht124b, ht024c, hbg2b, hbg4]
                        ·
                          linarith only [hdelta1, ht014b, ht123b, ht134b, hbg2b, hbg4]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, ht234b, hbg4, hbg2a]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht013b, ht014b, ht034a, ht024c, hbg1, hbg2b, hbg4]
                          ·
                            linarith only [hdelta1, ht014b, ht123b, ht024c, hbg1, hbg2b]
                          ·
                            linarith only [hdelta1, ht012e, hbg1, ht234a, hbg4, hbg2a]
                          ·
                            linarith only [hdelta1, ht012b, ht014a, hbg1, ht234a, hbg4, hbg2a]
                          ·
                            linarith only [hdelta1, ht014b, ht024c, hbg2b, hbg1c]
                          ·
                            linarith only [hdelta1, ht012e, ht134b, ht234b, hbg2c, hbg1c]
                          ·
                            linarith only [hdelta1, ht013a, hbg1c]
                          ·
                            linarith only [hdelta1, ht012e, ht123b, ht234b, hbg2c, hbg1c]
                          ·
                            linarith only [hdelta1, ht014a, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht012b, ht234a, hbg4, hbg2a, hbg1c]
                        ·
                          linarith only [hdelta1, ht123b, ht134b, hbg2b, hbg4c]
                        ·
                          linarith only [hdelta1, ht024c, ht134e, hbg4c]
                        ·
                          linarith only [hdelta1, ht012b, ht024c, ht234a, hbg2c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht134e, hbg4c]
                        ·
                          linarith only [hdelta1, ht012b, ht014b, ht234a, hbg2c, hbg4c]
                        ·
                          have hb1 := m.budget 1 (by decide) 2 3 4 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, h120, h341, ht013b, ht023c, ht234b, hbg1, hbg4a]
                          ·
                            linarith only [hdelta1, h130, h341, ht014b, ht024c, hbg1, hbg4a]
                          ·
                            linarith only [hdelta1, ht012e, ht234b, hbg2a, hbg1, hbg4c]
                          ·
                            linarith only [hdelta1, ht012b, ht014a, ht234b, hbg2a, hbg1, hbg4c]
                          ·
                            linarith only [hdelta1, h011, h120, ht014a, hbg1c]
                          ·
                            linarith only [hdelta1, ht012e, ht134b, hbg1c, ht234b, hbg2c]
                          ·
                            linarith only [hdelta1, ht014a, ht134b, hbg1c]
                          ·
                            linarith only [hdelta1, ht012e, ht123b, hbg1c, ht234b, hbg2c]
                          ·
                            linarith only [hdelta1, ht014a, ht123b, hbg1c]
                          ·
                            linarith only [hdelta1, ht012b, hbg1c, ht234b, hbg2a, hbg4c]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, hbg2c]
                    ·
                      have hb3 := m.budget 3 (by decide) 1 0 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc30, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht034a, ht123e, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht013b, ht123e, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, ht123e, hbg3]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, h120, h231, ht123b, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht034a, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht023e, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, hbg3c]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb3 := m.budget 3 (by decide) 1 4 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc30, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013d, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht023c, ht123e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht123e, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023c, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht123e, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123e, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013b, ht023c, ht134a, ht234a]
                    ·
                      have hb1 := m.budget 1 (by decide) 2 4 3 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc10] at hb1
                      rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                        ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                      ·
                        have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc21, hc20] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h120, ht013a, ht024a, ht234d, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht024a, ht134a, ht234d, hbg3, hbg2]
                          ·
                            linarith only [hn, hdelta1, h120, h231, ht013b, hbg3, ht134c, hbg1]
                          ·
                            linarith only [hdelta1, h011, h120, ht013a, ht023a, ht134a, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, hbg3b, ht134c, hbg1]
                          ·
                            linarith only [hdelta1, h120, h231, ht023b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, h011, h120, ht013a, ht024a, ht234c, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, h120, h231, ht023b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, h031, h120, hbg3a, ht134c, hbg1]
                          ·
                            linarith only [hdelta1, h120, h231, ht013b, hbg3a, ht134c, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012e, ht013a, ht234d, hbg2, hbg3]
                          ·
                            linarith only [hn, hdelta1, h031, h120, ht134c, hbg1, hbg3]
                          ·
                            linarith only [hn, hdelta1, h120, h231, ht013b, ht134c, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht013a, ht134a, ht234c, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h031, h120, ht134c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, h120, h231, ht013b, ht134c, hbg1, hbg3b]
                          ·
                            linarith only [hdelta1, ht012e, ht013a, ht234c, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, h031, h120, ht134c, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h031, h120, ht134c, hbg1, hbg3a]
                          ·
                            linarith only [hdelta1, h120, h231, ht013b, ht134c, hbg1, hbg3a]
                        ·
                          linarith only [hdelta1, h120, h231, ht012e, ht013a, ht024a, ht134c, hbg2, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht023a, ht134c, hbg2, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h120, ht013a, ht234d, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht134a, ht234d, hbg3, hbg2c]
                          ·
                            linarith only [hn, hdelta1, h120, h231, ht013b, hbg3, ht134c, hbg1]
                          ·
                            linarith only [hdelta1, h011, h120, ht013a, ht134a, ht234c, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, hbg3b, ht134c, hbg1]
                          ·
                            linarith only [hdelta1, h120, h231, ht014b, ht034c, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, h011, h120, ht013a, ht234c, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h231, hbg3a, hbg3b, ht134c, hbg1]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, hbg3a, ht134c, hbg1]
                          ·
                            linarith only [hdelta1, h120, h231, ht013b, hbg3a, ht134c, hbg1]
                        ·
                          linarith only [hdelta1, h120, h231, ht014b, ht024c, hbg1, hbg2b]
                        ·
                          linarith only [hdelta1, ht013b, ht023c, ht134c, hbg1, hbg2b]
                        ·
                          linarith only [hdelta1, h120, h231, ht014b, ht024c, hbg1, hbg2b]
                        ·
                          linarith only [hdelta1, ht014b, ht023c, ht034c, hbg1, hbg2b]
                        ·
                          linarith only [hdelta1, h120, h231, ht014b, ht024c, hbg2a, hbg1]
                      ·
                        have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc21, hc20] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, h011, h120, ht013a, ht024a, ht124e, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht234d, ht134b, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, h140, h231, ht012e, ht013a, ht024a, hbg1, hbg2]
                        ·
                          linarith only [hn, hdelta1, ht013b, ht023c, ht124b, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, h011, h120, ht013a, ht234d, ht134b, hbg2c, hbg1]
                        ·
                          linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, ht013b, ht023c, ht124b, hbg2b, hbg1]
                        ·
                          linarith only [hdelta1, h120, h231, ht012e, ht013a, ht124b, hbg2c, hbg1]
                        ·
                          linarith only [hdelta1, ht013b, ht023c, ht124b, hbg1, hbg2b]
                        ·
                          linarith only [hdelta1, ht013b, ht023c, ht124b, hbg1, hbg2b]
                      ·
                        have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc21, hc20] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, h011, h120, ht024a, ht134a, ht234d, hbg2, hbg1]
                        ·
                          linarith only [hdelta1, ht012e, ht134a, ht234d, hbg2, hbg1]
                        ·
                          linarith only [hdelta1, h231, h340, ht012e, ht024a, ht134a, hbg2, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h340, hbg1, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht023c, ht123b, hbg2, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht012b, ht023b, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht024a, ht134a, ht234c, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht014b, ht034c, ht124b, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht013b, ht123b, hbg3a, hbg2]
                        ·
                          linarith only [hdelta1, h011, h120, ht134a, ht234d, hbg2c, hbg1]
                        ·
                          linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, ht023a, hbg2c]
                        ·
                          linarith only [hdelta1, h231, h340, ht012e, ht134a, hbg2c, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h340, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht023c, ht124b, hbg2b, ht134c, hbg3]
                          ·
                            linarith only [hdelta1, ht013b, ht124b, hbg2b, ht134c, hbg3]
                          ·
                            linarith only [hdelta1, h011, h020, ht134a, ht234c, hbg2a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h340, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht124b, hbg2b, hbg3c, ht134c]
                          ·
                            linarith only [hdelta1, ht023c, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht012b, ht024a, hbg2c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc41, hc40, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht012b, ht013a, ht024a, ht234d, ht134c, hbg1, hbg4]
                        ·
                          linarith only [hn, hdelta1, ht013c, ht034c, ht124b, hbg1, hbg4]
                        ·
                          linarith only [hdelta1, ht013a, ht014b, ht134a, ht234d, ht124b, hbg1, hbg4]
                        ·
                          linarith only [hdelta1, ht012b, ht013a, ht024a, ht134a, hbg1, hbg4]
                        ·
                          linarith only [hdelta1, ht014c, ht124b, hbg1, hbg4b]
                        ·
                          linarith only [hdelta1, ht014b, ht234d, hbg4c]
                        ·
                          linarith only [hdelta1, ht012b, ht014a, ht024a, hbg4c, hbg1]
                        ·
                          linarith only [hdelta1, ht014c, ht124b, hbg4a, hbg1]
                        ·
                          linarith only [hdelta1, ht014c, ht124b, hbg4a, hbg1]
                        ·
                          linarith only [hdelta1, ht013a, ht014b, ht134a, ht124b, hbg4c, hbg1]
                      ·
                        linarith only [hdelta1, h011, h120, ht013a, hbg1c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc41, hc40, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h011, h340, hbg4, ht134c, hbg1b]
                        ·
                          linarith only [hdelta1, h031, h120, ht034c, hbg4, hbg1a]
                        ·
                          linarith only [hdelta1, h120, h231, ht014b, ht234c, hbg4, hbg1a]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h011, h120, ht024a, ht134a, hbg4, hbg1b, hbg2]
                          ·
                            linarith only [hdelta1, h011, h020, ht134a, hbg4, hbg1b, hbg2]
                          ·
                            linarith only [hdelta1, h120, h231, ht014b, ht024c, hbg2, hbg1a]
                          ·
                            linarith only [hdelta1, ht014b, ht023c, ht034c, hbg2, hbg1a]
                          ·
                            linarith only [hdelta1, h011, h120, ht134a, hbg2c, hbg4, hbg1b]
                          ·
                            linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, ht023a, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h231, ht012e, hbg2c, hbg1c, ht134c]
                          ·
                            linarith only [hdelta1, ht012e, ht234c, hbg2c, hbg1c, ht134c]
                          ·
                            linarith only [hdelta1, h011, h340, ht014b, ht134a, hbg2c, hbg1c, ht024c]
                        ·
                          linarith only [hdelta1, ht034d, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht234d, hbg4c]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h011, h120, ht024a, hbg4c, ht134c, hbg1b, hbg2]
                          ·
                            linarith only [hdelta1, h011, h020, hbg4c, ht134c, hbg1b, hbg2]
                          ·
                            linarith only [hdelta1, h231, h340, ht014b, ht024c, hbg4a, hbg2]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, hbg1c, ht134c, hbg2]
                          ·
                            linarith only [hdelta1, h011, h120, hbg4c, ht134c, hbg1b, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, ht023a, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h231, ht012e, hbg1c, ht134c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012e, ht234c, hbg1c, ht134c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012e, ht024a, hbg1c, ht134c, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h241, hbg4c, hbg1a]
                        ·
                          linarith only [hdelta1, h011, h120, ht134a, hbg1c, ht024c, hbg4c]
                        ·
                          linarith only [hdelta1, h011, h120, ht014b, ht134a, hbg1c, hbg4c]
                      ·
                        linarith only [hdelta1, ht014a, hbg1c]
                      ·
                        have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc21, hc20] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, h011, h120, ht024a, ht124e, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, ht012e, ht234d, ht134b, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, h140, h231, ht012e, ht024a, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, ht012e, ht023a, ht124b, hbg1c, hbg2]
                        ·
                          linarith only [hdelta1, h011, h120, ht234d, ht134b, hbg1c, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, ht023a, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h231, ht012e, ht124b, hbg1c, hbg2c]
                        ·
                          linarith only [hdelta1, ht012e, ht234c, ht124b, hbg1c, hbg2c]
                        ·
                          linarith only [hdelta1, ht014e, ht124b, hbg1c, ht024c, hbg2c]
                      ·
                        linarith only [hdelta1, ht013a, ht124b, hbg1c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc41, hc40, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h011, h340, hbg1a, ht134c, hbg4]
                        ·
                          linarith only [hdelta1, ht013c, ht034c, ht124b, hbg1b, hbg4]
                        ·
                          linarith only [hdelta1, ht014b, ht134a, ht234d, ht124b, hbg1c, hbg4]
                        ·
                          linarith only [hdelta1, ht012b, ht024a, ht134a, hbg1c, hbg4]
                        ·
                          linarith only [hdelta1, ht234d, ht024c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht234d, hbg4c]
                        ·
                          linarith only [hdelta1, ht012b, ht024a, hbg1c, hbg4c, ht134c]
                        ·
                          linarith only [hdelta1, ht123e, ht234c, ht124b, hbg1c, hbg4c]
                        ·
                          linarith only [hdelta1, ht134a, ht124b, hbg1c, ht024c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht134a, ht124b, hbg1c, hbg4c]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht023b, ht024c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 1 4 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h120, h231, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123e, ht134a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht123e, ht134a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123b, ht134a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, h120, h231, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h130, h231, ht134a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123b, ht134a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123b, ht134a, ht234b, hbg2c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013b, ht023c, ht234a, ht134a]
                    ·
                      have hb2 := m.budget 2 (by decide) 1 4 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h120, h231, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, h120, h231, ht023a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h120, h231, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h120, h231, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h231, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht124a, hbg2c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht123b, ht124c, ht134b]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht012b, ht023a, ht124c, ht134b, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 1 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht012b, ht124a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht234e, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht234e, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h231, h340, ht124a, hbg2c, ht234b]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht124a, hbg2c]
              ·
                linarith only [ht012b, ht023a, ht123a]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 1 3 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h120, h241, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, h120, h341, ht024a, ht123a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, h120, h341, ht023a, ht123a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, h120, h341, ht024a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h341, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h341, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht013b, ht023c, ht024b, ht034c, ht134a]
                ·
                  linarith only [ht023a, ht024a, ht123a, ht124a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 1 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht024a, ht234d, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, ht234d, hbg2]
                      ·
                        linarith only [hdelta1, ht012b, ht123a, ht234d, hbg2]
                      ·
                        linarith only [hdelta1, ht012b, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht234d, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht234d, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h230, h341, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht123a, hbg2c]
                    ·
                      linarith only [ht013b, ht034a, ht123b, ht234a]
                  ·
                    linarith only [ht013b, ht023c, ht024b, ht034c, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
            ·
              linarith only [ht023c, ht024b, ht034c]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 1 3 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht023a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht124a, hbg2c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht123b, ht124c, ht134b]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 1 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht124a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht124a, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
                    ·
                      linarith only [ht013b, ht034a, ht123b, ht234a]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 4 1 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, ht124a, hbg2]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h230, ht012a, ht013b, ht034a, hbg2, hbg3, ht234e]
                        ·
                          linarith only [hdelta1, h011, h130, ht012a, ht034a, hbg2, hbg3, ht234e]
                        ·
                          linarith only [hdelta1, ht012a, ht013e, hbg2, hbg3, ht234e]
                        ·
                          linarith only [hdelta1, ht012a, ht013e, ht034a, hbg2, ht234b, hbg3]
                        ·
                          linarith only [hdelta1, h011, h230, ht012a, ht034a, hbg2, hbg3c, ht234e]
                        ·
                          linarith only [hdelta1, h011, h230, ht012a, ht013b, hbg2, hbg3c, ht234e]
                        ·
                          linarith only [hdelta1, ht013b, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h130, ht012a, hbg2, hbg3c, ht234e]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht012a, ht013e, hbg2, ht234b, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h230, ht012c, ht123c, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, ht034a, ht124a, hbg2, hbg3, ht234e]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, ht124a, hbg2, hbg3, ht234e]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, ht034a, ht123a, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht123c, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht123c, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht123c, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, ht124a, hbg2, hbg3c, ht234e]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, ht123a, hbg2, hbg3c]
                      ·
                        have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hn, hdelta1, ht014b, ht024c, ht123b, hbg2, hbg1]
                        ·
                          linarith only [hn, hdelta1, ht012b, ht124b, hbg2, ht234b, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h230, ht123c, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, h011, h130, ht034a, ht124a, hbg3, hbg1, ht234e]
                          ·
                            linarith only [hdelta1, ht013e, ht124a, hbg3, hbg1, ht234e]
                          ·
                            linarith only [hdelta1, ht013e, ht034a, ht123a, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht023c, hbg2, hbg3a, hbg3b]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, h011, h130, ht024c, ht034b, ht123a, hbg2, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, h011, h130, ht024c, ht034b, ht123a, hbg2, hbg3a, hbg1]
                          ·
                            linarith only [hdelta1, ht013e, ht124a, ht234b, hbg3c, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht013b, ht023c, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h240, h341, ht012a, ht034a, ht124a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht124a, hbg1, ht234e, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht034a, ht124a, ht234b, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht013b, ht024c, ht034b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht024c, ht034b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht024c, ht034b, ht123b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht024c, ht034b, ht123b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht124a, hbg3c, ht234b, hbg1]
                        ·
                          linarith only [hdelta1, ht012b, ht123b, hbg2, hbg1b, hbg1a]
                        ·
                          linarith only [hdelta1, ht014b, ht024c, ht123b, hbg2, hbg1a]
                        ·
                          linarith only [hdelta1, ht014b, ht024c, ht123b, hbg2, hbg1a]
                        ·
                          linarith only [hdelta1, ht012b, ht123b, ht134b, hbg2, hbg1a]
                        ·
                          linarith only [hdelta1, ht012b, ht123b, ht134b, hbg2, hbg1a]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h230, ht123c, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h011, h130, ht024c, ht034b, ht124a, hbg2, ht234b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, ht013b, ht124a, ht234e, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, ht124a, ht234b, hbg3, hbg1c]
                          ·
                            linarith only [hdelta1, ht023c, ht124a, hbg2, ht234b, hbg3b, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht024c, ht034b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht024c, ht034b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht024c, ht034b, ht123b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht024c, ht034b, ht123b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht124a, hbg3c, ht234b, hbg1c]
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht124a, hbg2c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht123c, hbg2b, hbg3]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht034a, ht123b, hbg2c, hbg3, ht234e]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, hbg2c, hbg3, ht234e]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, ht034a, ht234b, hbg2c, hbg3]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht034a, hbg2c, hbg3c, ht234e]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht013b, hbg2c, hbg3c, ht234e]
                        ·
                          linarith only [hdelta1, ht013b, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, hbg2c, hbg3c, ht234e]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, ht234b, hbg2c, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht013b, ht023c, hbg3, hbg2b]
                        ·
                          linarith only [hdelta1, ht024c, ht034b, ht123b, hbg3, hbg2b]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht014b, ht024c, ht123b, hbg1, hbg2b]
                          ·
                            linarith only [hdelta1, ht012b, ht123b, ht134b, hbg1, hbg2b]
                          ·
                            linarith only [hdelta1, h011, h230, ht234b, hbg1, hbg2a]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, hbg3, hbg1, hbg2a, ht234e]
                          ·
                            linarith only [hdelta1, ht012b, ht123b, hbg1c, hbg2b]
                          ·
                            have hb4 := m.budget 4 (by decide) 2 1 0 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc42, hc41, hc40, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, ht013e, ht014a, hbg3, ht234e, hbg4]
                            ·
                              linarith only [hdelta1, ht013b, ht013e, ht024c, ht124b, ht123b, hbg3, hbg2c, ht234e, hbg1b, hbg4]
                            ·
                              linarith only [hdelta1, h011, h130, ht014b, hbg1c, hbg2a, ht234e, hbg4]
                            ·
                              linarith only [hdelta1, ht013e, hbg3, hbg2a, hbg1b, hbg4]
                            ·
                              linarith only [hdelta1, ht013e, ht024c, ht123b, hbg1c, hbg3, hbg2c, ht234e, hbg4b]
                            ·
                              linarith only [hdelta1, ht014b, hbg4c, ht234e]
                            ·
                              linarith only [hdelta1, ht012b, ht013b, ht123b, hbg3, hbg2c, hbg4b]
                            ·
                              linarith only [hdelta1, h011, h240, ht024c, ht123b, hbg1c, hbg2c, hbg4a]
                            ·
                              linarith only [hdelta1, h011, h240, ht024c, ht123b, hbg1c, hbg2c, hbg4a]
                            ·
                              linarith only [hdelta1, ht012b, ht013e, ht123b, hbg1c, ht124c, hbg3, hbg2c, hbg4b]
                          ·
                            linarith only [hdelta1, ht012a, hbg1c, ht124c]
                          ·
                            linarith only [hdelta1, ht013e, ht134e, hbg1c, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht134b, hbg1c]
                          ·
                            linarith only [hdelta1, h240, h341, ht013b, hbg1c, hbg3, hbg2a]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht013e, ht014a, ht034a, ht123b, hbg3, hbg1]
                          ·
                            linarith only [hdelta1, ht012b, ht124b, ht234b, hbg1, hbg2b]
                          ·
                            linarith only [hdelta1, ht013e, ht034a, hbg3, ht234b, hbg2a, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht034a, hbg3, ht234b, hbg2a, hbg1]
                          ·
                            linarith only [hdelta1, ht014b, ht034c, ht123b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, ht014b, ht034c, ht123b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, ht014b, ht034c, ht123b, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, ht013e, ht034a, ht124b, hbg3, ht234b, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, ht134b, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, ht123a, hbg3, hbg1c]
                        ·
                          linarith only [hdelta1, ht024c, ht034b, hbg3c, hbg2b]
                        ·
                          linarith only [hdelta1, ht012b, ht013b, hbg3c, hbg2c, ht234e]
                        ·
                          linarith only [hdelta1, ht013b, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht012b, ht123b, hbg3c, hbg2c, ht234e]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          have hb1 := m.budget 1 (by decide) 3 4 2 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc10] at hb1
                          rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                            ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                          ·
                            linarith only [hdelta1, ht014b, ht034c, ht123b, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht012b, ht124b, ht234b, hbg1, hbg2b]
                          ·
                            linarith only [hdelta1, h011, h230, ht234b, hbg2a, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, hbg3c, ht234b, hbg2a, hbg1]
                          ·
                            linarith only [hdelta1, ht012b, ht123b, hbg1c, hbg2b]
                          ·
                            linarith only [hdelta1, ht013e, ht123b, hbg3c, ht124c, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, ht124c, hbg1c]
                          ·
                            linarith only [hdelta1, ht013e, ht123b, ht134b, hbg3c, hbg1c]
                          ·
                            linarith only [hdelta1, ht012a, ht134b, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht123a, hbg3c, hbg1c]
                      ·
                        linarith only [hdelta1, ht124a, ht234b, hbg2c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 1 3 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht023a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht023c, ht034a, ht123a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, ht123a, hbg2, ht234a]
                      ·
                        linarith only [hdelta1, ht012d, ht023c, ht034a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, hbg2c, ht234b]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, hbg2c, ht234a]
                      ·
                        linarith only [hdelta1, ht012d, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht124a, hbg2c]
                    ·
                      have hb2 := m.budget 2 (by decide) 1 4 3 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123b, ht134a, hbg2, ht234a]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h120, ht012c, ht123b, ht134a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123b, ht134a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, hbg2c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht134a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 1 4 3 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht124a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, hbg2c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht123b, ht124c, ht134b]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht134a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 1 3 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht023a, ht123a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht123a, ht124a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht023a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 1 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h021, h230, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023d, ht034a, ht123a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, ht123a, ht124a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, ht023d, ht034a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, ht124a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, hbg2c]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
                    ·
                      linarith only [ht123a, ht124b, ht234a, ht134c]
                  ·
                    linarith only [ht123c, ht124b, ht134c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 1 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc31, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht023d, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht013d, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht023d, ht123b, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht123b, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023d, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023d, hbg3c, ht134a]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c, ht134a]
                      ·
                        linarith only [hdelta1, ht013d, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123b, hbg3c]
                      ·
                        linarith only [hdelta1, ht123b, hbg3c, ht134a]
                    ·
                      linarith only [ht123b, ht234a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 4 1 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc31, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, ht123c, hbg3, ht134a]
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, ht123c, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht023d, hbg3, ht234a, ht134a]
                      ·
                        linarith only [hdelta1, ht013b, hbg3, ht234a, ht134a]
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht023d, hbg3c, ht134a]
                      ·
                        linarith only [hdelta1, ht013b, hbg3c, ht134a]
                      ·
                        linarith only [hdelta1, ht023d, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht234a, hbg3c, ht134a]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 3 1 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h011, h340, ht012a, ht123a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, h011, h340, ht012a, ht234a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht123a, ht234a, hbg2]
                      ·
                        have hb1 := m.budget 1 (by decide) 4 3 2 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hn, hdelta1, ht012b, ht123c, ht124b, hbg1, hbg2]
                        ·
                          linarith only [hdelta1, h011, h340, ht012a, ht123b, ht234a, hbg1]
                        ·
                          linarith only [hdelta1, h011, h340, ht123a, ht234a, hbg1]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht012a, ht123a, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht013b, ht023c, ht234c, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, ht012a, ht023c, ht123b, ht124a, ht234a, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht014b, ht034c, ht123a, ht234a, hbg1, hbg3]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, ht234c, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, ht234c, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht123a, ht134c, hbg1, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht134c, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, ht234c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, ht234c, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, ht012b, ht123b, ht234c, hbg1b, hbg2]
                        ·
                          linarith only [hdelta1, ht013b, ht023c, ht124b, hbg1a, hbg2]
                        ·
                          linarith only [hdelta1, ht013b, ht023c, ht124b, hbg1a, hbg2]
                        ·
                          linarith only [hdelta1, ht012b, ht123b, ht234c, hbg1a, hbg2]
                        ·
                          linarith only [hdelta1, ht012b, ht123b, ht234c, hbg1a, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht123a, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h011, h230, ht123c, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, ht013c, hbg3, ht134c, hbg1b]
                          ·
                            linarith only [hdelta1, ht013b, ht123a, hbg3, ht234a, ht134c, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, ht234c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, ht234c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht013b, ht123a, ht134c, hbg1c, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht123a, ht234c, ht134c, hbg3b, hbg1c, hbg2]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, ht234c, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, ht234c, hbg3a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h340, ht012a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht234a, hbg2c]
                      ·
                        have hb1 := m.budget 1 (by decide) 4 3 2 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc10] at hb1
                        rcases hb1 with hbg1 | hbg1 | hbg1 | hbg1 |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ |
                          ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩ | ⟨hbg1a,hbg1b,hbg1c⟩
                        ·
                          linarith only [hdelta1, ht012b, ht123c, ht124b, hbg1, hbg2b]
                        ·
                          linarith only [hdelta1, h011, h340, ht012a, ht123b, ht234a, hbg1]
                        ·
                          linarith only [hdelta1, h011, h230, hbg1, hbg2a]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht012a, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, ht234c, hbg2b, hbg3]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, ht234c, hbg2b, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht234a, ht134c, hbg1, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, ht012a, ht123c, hbg3c]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht134c, hbg3b, hbg1]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, hbg3c, ht134c, hbg1, hbg2a]
                          ·
                            linarith only [hdelta1, ht012a, ht023c, ht234c, ht134c, hbg1, hbg3b, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht012a, ht023c, ht234c, ht134c, hbg1, hbg3a, hbg2c]
                        ·
                          linarith only [hdelta1, h011, h140, ht012a, hbg1c]
                        ·
                          linarith only [hdelta1, h011, h340, ht013b, ht023c, ht124b, ht234a, hbg2c, hbg1c]
                        ·
                          linarith only [hdelta1, ht013a, hbg1c]
                        ·
                          linarith only [hdelta1, h011, h340, ht123b, ht234a, hbg1c]
                        ·
                          linarith only [hdelta1, ht012a, ht134c, hbg1c]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, hbg3, hbg2a, hbg1a]
                          ·
                            linarith only [hdelta1, h011, h340, ht123c, ht234a, hbg3, hbg1a]
                          ·
                            linarith only [hdelta1, h011, h340, ht023c, ht124a, ht234a, ht134c, hbg3, hbg1a, hbg2c, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht234a, ht134c, hbg3, hbg2a, hbg1c]
                          ·
                            linarith only [hdelta1, h011, h340, ht123c, hbg3c, hbg1a]
                          ·
                            linarith only [hdelta1, ht023c, ht234c, ht134c, hbg2c, hbg1c, hbg3b]
                          ·
                            linarith only [hdelta1, ht013b, hbg3c, ht134c, hbg2a, hbg1c]
                          ·
                            linarith only [hdelta1, ht023c, ht234c, ht134c, hbg3b, hbg2c, hbg1c]
                          ·
                            linarith only [hdelta1, ht013b, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht234c, ht134c, hbg3a, hbg2c, hbg1c]
                      ·
                        linarith only [hdelta1, ht123a, ht234c, hbg2c]

#print axioms model_impossible_0
end Jsp404.GlobalFiveLowTerminal
