import Jsp000404.SixExactFloorKernelSymbolicMask000Probe
import Jsp000404.SixExactFloorKernelSymbolicMask011Probe
import Jsp000404.SixExactFloorKernelSymbolicMask011Reflection
import Jsp000404.SixExactFloorKernelSymbolicMask031Probe
import Jsp000404.SixExactFloorKernelSymbolicMask031Reflection
import Jsp000404.SixExactFloorKernelSymbolicMask064Probe
import Jsp000404.SixExactFloorKernelSymbolicMask075Probe
import Jsp000404.SixExactFloorKernelSymbolicMask075Reflection
import Jsp000404.SixExactFloorKernelSymbolicMask079Probe
import Jsp000404.SixExactFloorKernelSymbolicMask079Reflection
import Jsp000404.SixExactFloorKernelSymbolicMask127Probe
import Jsp000404.SixExactFloorKernelSymbolicMask127Reflection
import Jsp000404.SixExactFloorKernelSymbolicMask202Probe
import Jsp000404.SixExactFloorKernelSymbolicMask202Reflection
import Jsp000404.SixExactFloorKernelSymbolicMask222Probe
import Jsp000404.SixExactFloorKernelSymbolicMask222Reflection
import Jsp000404.SixExactFloorKernelSymbolicMask255Probe
import Jsp000404.SixExactFloorKernelSymbolicMask255Reflection
import Jsp000404.SixExactFloorKernelSymbolicMask567Probe
import Jsp000404.SixExactFloorKernelSymbolicMask567Reflection
import Jsp000404.SixExactFloorKernelSymbolicMask575Probe
import Jsp000404.SixExactFloorKernelSymbolicMask575Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask003Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask003Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask007Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask007Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask015Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask015Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask072Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask072Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask095Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask095Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask1023Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask200Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask216Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask218Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask218Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask223Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask223Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask254Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask254Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask510Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask511Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask511Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask515Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask515Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask519Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask519Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask551Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask551Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask807Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask823Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask831Probe
import Jsp000404.SixExactFloorKernelSymbolicV2Mask831Reflection
import Jsp000404.SixExactFloorKernelSymbolicV2Mask959Probe
import Jsp000404.SixSymbolicLegacyReuse

/-! Complete original ten-triangle disjunction coverage for all n>=4. -/
set_option pp.fullNames true
namespace Jsp404.SixExactFloorKernel

set_option maxHeartbeats 16000000 in
theorem symbolic_between_impossible {n : ℕ} (M : SixModelCompression.ModelSix n)
    (hn4 : 4 ≤ n) (hhigh : (1 / 2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    : False := by
  rcases M.triangle 0 1 2 (by decide) (by decide) with htri012 | htri012
  ·
    have htr012a := htri012.1
    have htr012b := htri012.2.1
    have htr012c := htri012.2.2
    rcases M.triangle 0 1 3 (by decide) (by decide) with htri013 | htri013
    ·
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      rcases M.triangle 0 1 4 (by decide) (by decide) with htri014 | htri014
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask0_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask512_legacy_reuse M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123c, htr134a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask768_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134b, htr123b, htr124c]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134b, htr123a, htr124c, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask896_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask64_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr124b, htr234a, htr134c, htr123a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr124b, htr123c, htr134c]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask192_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123b, htr234a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask448_legacy_reuse M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask960_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask800_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr134a, htr034a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask928_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr123c, htr134c, htr124b]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask992_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr023b, htr034b, htr024c]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask944_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr023a, htr024a, htr124a, htr123a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask1008_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask72_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013c, htr023b, htr134a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134c, htr123c, htr124b]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask200_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023a, htr024a, htr134c, htr124b, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask456_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023a, htr024b, htr234a, htr034c]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr024b, htr034c, htr023c]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr124a, htr012c]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask216_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013c, htr023b, htr234a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask472_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013c, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask504_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask1016_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr012b, htr014c, htr024b]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr023b, htr012b, htr014c, htr034b]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134b, htr014a, htr012a, htr234a, htr123a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask948_legacy_reuse M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr023a, htr123a, htr124a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr134a, htr034a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr014a, htr023a, htr012b, htr234a, htr134b]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask1012_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr013b, htr023c, htr024b, htr014c]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr013b, htr014c, htr034b]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr123a, htr012c, htr023a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013c, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask508_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask1020_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
    ·
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      rcases M.triangle 0 1 4 (by decide) (by decide) with htri014 | htri014
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr023b, htr013c, htr012b]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask74_legacy_reuse M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr234a, htr013a, htr012a, htr123b, htr134c, htr124b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask202_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr024a, htr013a, htr012b, htr234a, htr134c, htr123b, htr124b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr034c, htr013c, htr012b, htr024b]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr012c, htr024a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask218_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr014a, htr013a, htr123b, htr234a, htr134c]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr014b, htr034c, htr013c]
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr013c, htr012b, htr023b]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr014c, htr012b, htr024b]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012c, htr023a, htr123a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr024a, htr012c]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask222_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr034a, htr013b, htr234a, htr123b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr123a, htr012c, htr023a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr024a, htr012c]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask254_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134a, htr234a, htr123b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask510_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask1022_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
  ·
    have htr012a := htri012.1
    have htr012b := htri012.2.1
    have htr012c := htri012.2.2
    rcases M.triangle 0 1 3 (by decide) (by decide) with htri013 | htri013
    ·
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      rcases M.triangle 0 1 4 (by decide) (by decide) with htri014 | htri014
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask1_legacy_reuse M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask513_legacy_reuse M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr234a, htr123c, htr134a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask769_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012b, htr124a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr123a, htr023a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr134a, htr034a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013c, htr123c, htr234a, htr034a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask801_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr024a, htr012b]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr023a, htr123a]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr012c, htr014b, htr024c]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr012c, htr013b, htr023c]
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr013b, htr034b, htr014c]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr014a, htr013a, htr134b, htr123c, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask805_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012b, htr124a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012b, htr123a]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr012c, htr013b, htr024c, htr034b]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr012c, htr234a, htr013a, htr024a, htr124c, htr123c, htr134b]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask821_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013a, htr134b, htr012a, htr123c, htr234a, htr124c]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask949_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr123a, htr012b]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr012c, htr023c, htr013b]
    ·
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      rcases M.triangle 0 1 4 (by decide) (by decide) with htri014 | htri014
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask3_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask515_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012b, htr124a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012b, htr123a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr014b, htr034c, htr013c]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr014b, htr024c, htr023b, htr013c]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask11_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr012c, htr134c, htr014a, htr023a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr134a, htr034a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr123a, htr023a, htr024a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask75_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134c, htr123a, htr012a, htr014a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr134a, htr034a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr012b, htr124a, htr024a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr012c, htr023c, htr034c, htr014b]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr012c, htr014b, htr024c]
      ·
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        rcases M.triangle 0 2 3 (by decide) (by decide) with htri023 | htri023
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask7_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask519_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr134a, htr034a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr012b, htr124a, htr024a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr023a, htr123a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask551_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013b, htr023c, htr134a, htr234a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask807_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr012b, htr024a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr123a, htr012b, htr023a]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr034b, htr024c, htr023b]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr034b, htr234a, htr023a, htr024c]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask567_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr024a, htr234a, htr023a, htr134b, htr124c]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask823_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134b, htr124c, htr123b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013b, htr234a, htr023c, htr134a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask951_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr123a, htr023a]
        ·
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          rcases M.triangle 0 2 4 (by decide) (by decide) with htri024 | htri024
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask15_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr123a, htr023a, htr024a, htr124a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask79_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr012b, htr024a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr023c, htr024b, htr034c]
          ·
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            rcases M.triangle 0 3 4 (by decide) (by decide) with htri034 | htri034
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask31_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr234a, htr023b, htr034a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr124c, htr123b, htr134b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask95_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr234a, htr034a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134a, htr013b, htr034a]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask223_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
            ·
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              rcases M.triangle 1 2 3 (by decide) (by decide) with htri123 | htri123
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask63_legacy_reuse M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask575_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123c, htr234a, htr134a]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask831_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr123b, htr134b, htr124c]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123a, htr234a, htr134b, htr124c]
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask959_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
              ·
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                rcases M.triangle 1 2 4 (by decide) (by decide) with htri124 | htri124
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask127_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134c, htr124b, htr123a, htr234a]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134c, htr123c, htr124b]
                ·
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  rcases M.triangle 1 3 4 (by decide) (by decide) with htri134 | htri134
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_mask255_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134a, htr234a, htr123b]
                  ·
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    rcases M.triangle 2 3 4 (by decide) (by decide) with htri234 | htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask511_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234
                    ·
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      exact Jsp404.SixExactFloorKernel.symbolic_v2_mask1023_probe M hn4 hhigh hdef0 hdef1 hdef3 hdef4 htri012 htri013 htri014 htri023 htri024 htri034 htri123 htri124 htri134 htri234

#print axioms symbolic_between_impossible
end Jsp404.SixExactFloorKernel
