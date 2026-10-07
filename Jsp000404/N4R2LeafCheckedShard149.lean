import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard149
open N4R2RowDataReplay

-- Original cycle 000f49d7e18f9d0c1459be9e5548a3825bed51e92546704874de034984a8adea; original global index 7.
def localCycle00000 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 14 1]

-- Original cycle 00f543f1cc207dec67d6853b73099f0de882102938f28396a4a93bce52327002; original global index 81.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle 02f625b59ab0912b57985c8267e54f08536a5930c762fa9b95c09caf0999da9d; original global index 239.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 5 0, .triangle 8 0, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .gapLower 2 0]

-- Original cycle 03799ecc70e808157594e100a4c7dc80fdcd9178b0047a289fa617c118cf9e5e; original global index 280.
def localCycle00003 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -3, 3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle 0416c8521b8cb3b9c839251abb8cadb4fe4d8d6d5f8a7cc8dc678d3b0d5c9717; original global index 321.
def localCycle00004 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 04b93c44f21ff37b2ee091bb867687f381a863d91686fde344ec3767465edf6c; original global index 378.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 05b89de46c21246fc3aedf02a26ce41bfdbe9c79eeed4d4005ba8f6007ee1a22; original global index 473.
def localCycle00006 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle 0641e07500445041b59814106127ba3600d59e94c8e9d0cae47f4d2899d7fe67; original global index 517.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 07ee492af53154bfeac4dca9a6f4b650194af222865004346666db34f9311aef; original global index 641.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle 081eb02c54c1f16717cd42389e9ae07deb0420e03416bcc0e56133f79775a9e4; original global index 651.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0864ac763342c1313ea099ae3fa403119a818bce42fbe2307fe463568cd43be3; original global index 666.
def localCycle00010 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -2, 3, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 30 2, .gapLower 6 4, .triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle 09efbfdf62817d8f431e34af0ae4483758af396907b560b58c73525e94ebab8a; original global index 800.
def localCycle00011 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false] }
  origin := ![.gapUpper 2 1, .triangle 28 1, .triangle 31 0, .triangle 19 0, .gapLower 1 1]

-- Original cycle 0be7da34af8deec17e927246e10000bc24a43d8df3bf27abcd9c472fe390345a; original global index 946.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 32 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 115fbe86a5606ae79af63d368e734d2249119a9d391d6f0fa62770d2cc17a4cb; original global index 1384.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 3, .gapLower 6 2, .triangle 21 1, .gapLower 3 0]

-- Original cycle 11b3cf73cd10f7a0645ba5b5a7030b2e0999f1fc336840cb4c8313f15b98f445; original global index 1412.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 146ed8522528620b821f7324c121e34825862796cdd8efc56937054cd67e618d; original global index 1613.
def localCycle00015 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -2, 2, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle 1511e00c9475d1ce0f888d4d8cbe6a7972aa265c1b2d3383a13bec9288623d25; original global index 1670.
def localCycle00016 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 188fbdd84528286b348e075f12abb42b55a4b126b30f35637951c012d798a4fe; original global index 1922.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 189d3bef0c01ed8a8d4349e5ce4c668f9c2af0ffc79bded23a1aa158bda4f71a; original global index 1926.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 1df162b8972b601818ceaad22ebede39ebcfb64183ac16a161674e4d4e2553b9; original global index 2300.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 2, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 218af6d29bb0e417e66fb43dde39c420eabc8deb5f405cc724aab2c797a5dc39; original global index 2569.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 22c551238c75cfff6ef46c0b386db68a3bc43ef8a18488ddc31263acf4e9764c; original global index 2663.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 2318b5c9d4a5617c95bf572a3b7fbdd7c5c8013eec75909775b3eb35ec9c46eb; original global index 2695.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 23de766382fe7b8af0800384bf1c3bc90852f8c728343b3d8ced53b1622fde0c; original global index 2748.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .gapLower 4 1, .gapLower 1 2, .gapLower 3 0]

-- Original cycle 24b6900874ed97277acb8aba90cf299d96676b5e058ff5172f0ea8740d48d777; original global index 2815.
def localCycle00024 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 8 2, .triangle 14 1]

-- Original cycle 27bc48cf3aaf11e2edd9dc0c136a9c2a7b52b75e24a1b0a0890ce83204e50d5a; original global index 3035.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 13 2, .gapLower 6 3, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 27f04f2d6552e1527407cf56e7fa18c30dfa8a04bac74e5036a5210f5889f074; original global index 3057.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .gapLower 4 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 28266a02a079878cf64ae46ec2b193b19a78c1c77380e90e6eb4f9d86588583f; original global index 3071.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 2987fd91a816e5bf10507f29c982d2003dc5023598815027b17ad36f75c95fbb; original global index 3165.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 4, .triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 2a3c7a9460ef55771cdef48241251ddffac8f7cdcd4a95887a330ef08986a74e; original global index 3217.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 22 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2c3cb984c3cd840e1b3667f7470d0089592ba6d7b08e86b31b021ab5c893bfe0; original global index 3385.
def localCycle00030 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 6 0]

-- Original cycle 2e93be7e67bc714bcd09687bd31f18d5b011b3edfc8d668925e3e7edff00833e; original global index 3559.
def localCycle00031 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 30650273b9b4fafeb3e8c1a5925a6ebabfa2218602b7dde61126c026d018d6a5; original global index 3684.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 2, .triangle 23 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 32a67e870b53a94a586fd31ce004b42cc80aee10db774635cbf68be88c402077; original global index 3875.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 35e64640f9dcd4d2556f61ae44bf2c16db791631bdb695cc2cbcf90c5be745cf; original global index 4135.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 376136bac05f21e1819da0672008ef85bb408a6a97e12e1be187ce93b2f53f29; original global index 4255.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle 394bed5e388ea5aa8eaf5047cd6d1faa2bc4cb2545a7392d960c9f991448e179; original global index 4409.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Original cycle 3a75ae0405f43dbf45d698042d232df7294a99000a41120c49bf5aef55f94af7; original global index 4512.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 3b123d0a37fc89ecaa915a15b445503d9b1e7e8d93b922b3f6194901bba46cfd; original global index 4566.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 32 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 3e2e6579eec88f8fce8b58b368acf1500a00b4e7af6add8a11e863a8f1c8a5b1; original global index 4813.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Original cycle 4141ec5f068a3eee408832b5f013aed5f2a98c12a8b7aaba693baf40e120ed4a; original global index 5039.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 42f345d7a8496c8fb24ddde75a362b9bcd98b51f25d88fd2f786234e07fa2ed2; original global index 5159.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 43a3cd6445f65d532c3ea0bdd7d35eba550a12954132020e0fd677eb780f458f; original global index 5232.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle 447dce25b2412ddcb8c4dd1a58bc35595013acb8a0bcf8b9142941bd6294c8fd; original global index 5300.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 44bfb42fc186bd13a523bd5eae0205b5b224f3a649eeb7469689fad00c8847f3; original global index 5328.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 46444650b8676f029efc9495cfab142bab6a0266339153bc55e99b0925cd2289; original global index 5436.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 483afca35d22cdefa6d7e96337014cd3a47686cfbbe43ca08f59fa4a9cecd947; original global index 5591.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 4, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4b7bd37c6e84c406c77873846ba8aabe838384d43343dea6929399ba0b625734; original global index 5851.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 4b8c8e7e99eee5d0531c5c6a9da7d65a0aa52d16724c2750f6945f8ad0cd63a7; original global index 5860.
def localCycle00048 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 3 6, .distance 1 6, .theta 1]
    constant := ![3, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 32 2, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 4c0d20dcab4f65cb13909f1ba605e2e0d4adc88ad7d39be3c24f2b612e807f9d; original global index 5903.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 4e478a55e76a193867d4a93e19249529f55f731191fb653037c1dbaafdc74a06; original global index 6077.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 8 0, .triangle 30 1, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4feffdd020a31c85a721d0811084c459025ba3e53028c98fa9182c2425e83892; original global index 6206.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 8 2, .gapLower 6 3, .triangle 21 2, .triangle 23 1, .gapLower 6 0]

-- Original cycle 50c9e5f343ac77a5f4e6a9e35be2069cc0d6843b190732de605cc64389cd6fdf; original global index 6274.
def localCycle00052 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 8 1]

-- Original cycle 52c3f8b9f2e560bf26767f27de0486b4af0406a44e3911c463a9d662244bfc93; original global index 6436.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 583b1477da0d6bab822620d7c56b8d488710aa586218a66677d1f16be99cd648; original global index 6846.
def localCycle00054 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, 2, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 10 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 594301ca6a5636ef3da87c63966bd4b8295f4c6d6a9b9733c301b2fde88b7cd4; original global index 6925.
def localCycle00055 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 5c10e42421b10806d37b0ef22e0bcd2159ee12f61fb6c27291ad4e07339bc25f; original global index 7166.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 5ce7ff1d9867eb40a7a1468dc3ae22fca7b1e1b91e8695d956dff524cd384607; original global index 7232.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 11 2, .triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5d1ab38248f0d351f2089efa6ebf995f0c52e7096a2c8e5cd4a11bdbab0b6fbe; original global index 7245.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 5e17f06a64692aa4f652982b241ddf395fb7606cb2a47f78d5ea5121516fe22c; original global index 7318.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 5e72e02d86b4dcf970b946c182f1d509b3c44ccea465874396a7e8054e853cca; original global index 7349.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .theta 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, -2, 0, 3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaNext 4, .corridorUpper 2 4, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5ea957d47df5f92c8ec8d319dab62a17731ef18f70280ee258548b474df996c2; original global index 7364.
def localCycle00061 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 3 6, .distance 1 6, .theta 1]
    constant := ![3, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 32 2, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 5eb27fceef2cc4e0691aa42b370bca44837b5da43e43bcc8058f1676c119a580; original global index 7368.
def localCycle00062 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle 620e90b1097c8d46ae02c70a7fe3bd69c5430ff59dbfca12049cbfe6bc88be78; original global index 7656.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 19 2, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 62dddbf106d5a200f6fcc623a15e9f3b1d634c127ad883631c7c264003addce2; original global index 7714.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 6374044bec23e2a1532346ee0abe9dbceeea32e022d5d7eb150658b06fad8c72; original global index 7761.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 65d989086be9882eb1b3157bf613723217bf33cc5b5226eaa6262b2dcd663676; original global index 7928.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 660b1595d38e65450ea5b0e73d8c35e5a5e0eab46a39c85fb59a49bc95029a4b; original global index 7941.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 11 1, .triangle 21 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 66af717d3cfe7979710baa3b9702049f0ffcbf42f3ed79a62eb8db1478cd341d; original global index 7982.
def localCycle00068 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 68621500b7cb74ec11ab090dc83e4c671c401611917cd478b5879c146b82111b; original global index 8118.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 6cae754eaa27f602e8725c14009577a0dc3f57f5d5ef66468299193575559001; original global index 8457.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 774baa635a942b8fefb75d2488a33555b8a77d59a3acbd6f6bab416bbc0205ac; original global index 9231.
def localCycle00071 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 28 1, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 7a4c9d9cab8486b71a7866e544e99bfff9c835020b1e94f3277433e0823b7a30; original global index 9459.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 7be9a353d8ec348345855a0df7a1dc5e30077adb599a300527a40a4cd1649763; original global index 9581.
def localCycle00073 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, 0, 2, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 24 2, .gapUpper 1 5, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .corridorLower 3 5]

-- Original cycle 7f6412be3fa67a3977e38cd73aac48d8976a17050d72976ff8d9b7cfb91c0048; original global index 9880.
def localCycle00074 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 14 1]

-- Original cycle 84cb6b6027885a9f0474caf9ff2333654247045d03101f5f3a07ef4da068d93f; original global index 10310.
def localCycle00075 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .gapLower 6 5, .triangle 8 0]

-- Original cycle 85f5bdd531b9f97cdfedd99ec5b54772b1553b662771357f43a580a9f68419aa; original global index 10393.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 8942a15d9ab75a443feb602e119e557726fe2b8eece348886bd03bae650a42f2; original global index 10623.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 899cf91c46259836e1f7e8d4d20e45ba00ecc663d32c6c3e582793512fdfb20b; original global index 10659.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 8c34a0113f3b0afae82c857e21406c1cc52833405c8d8a965b10b4c67c261ea8; original global index 10850.
def localCycle00079 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle 8c5db7d3e0a35b4a3ea5b4b038606ebe441a61fc58f8f42e4d8759de93aab21e; original global index 10862.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 2, .triangle 23 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 8d5ae7ca048a8b176227f22536a7d2ce861aa299d2ee119a034c3f0ab90dccbd; original global index 10930.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 926be3c990376188a81394d52b7586e57fba313dc9f8beb093e94dd78a09ec70; original global index 11339.
def localCycle00082 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 2, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 24 2, .gapUpper 1 5, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 939344c97282a2bb4a3f7af15bd0a731aa6a96d520d33281b951346e2612bb4f; original global index 11449.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 2, .gapUpper 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 9610deed76d3660981e192ec020544ba9f97dfbd1d9741c09f68d215c48f796c; original global index 11667.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 9a737df99cf76b529b5d27799ad1373f4ef68a5ef1cdffa62f617fc21f762705; original global index 12000.
def localCycle00085 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 14 1]

-- Original cycle 9e3e0fd7e3d6176e89e3e37b55345c3fd2e9359263f5f117c785bbd256529756; original global index 12318.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 9e50b18c428c8d9f38facc9bd560aebd312240acf6e05e2919facadbe2ae15c0; original global index 12325.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a0eaeaae8896551beda5214b43eb365d411fe99a89a6f3861d06ac36c33c7176; original global index 12517.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a2291d20b4996bf0e47936e86fed02b3cc694bdbc1aebf2770480dc855c942cf; original global index 12616.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 21 0, .gapLower 3 0]

-- Original cycle a4391f46c809a4dd828e640bfbcdaf0fc4bd46578b49a1702819abcbcf80aabb; original global index 12764.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 4, .triangle 27 1, .gapLower 6 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a5bad099acaab4c4e54bc0643be16ee25c4e176565edbbb4322631bc91f5659d; original global index 12874.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 6, .distance 3 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle a6c7f85f2a8cc73d3c615f9e1aaaf6d645f8990f72735ede2d967f3b079e9c95; original global index 12954.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle aa43858134f2f5d8ce87e48b93724d9d6bba64eae715a1a345a2efb799dd088a; original global index 13256.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle acc02c30038e54d54d91251d3ad862b9d82f45f2c6dc347b5fcf1f3ae969e591; original global index 13466.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle accfa8f9f8e26fbfc69cc1784329bf22fef854d1491c25598904197ed0200890; original global index 13473.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle acfab6aa2f1fc93540fed621b66deb7da26097b3d9306079430f4c6401c8f379; original global index 13482.
def localCycle00096 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle aeea6496ab8681b29e98f703b7e67d86b7a19cbdc423461ea33e9f05540495c1; original global index 13655.
def localCycle00097 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 1 2, .triangle 9 0, .triangle 31 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle b43f22d8fb78d5928020e8ea77626dda0a315c2dec4aead064b7a1878abb8f92; original global index 14078.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle b4e008cf3735cc7e29df6f98cb36047ca123b900146de4197e8861cdb9a85ac4; original global index 14126.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .gapLower 6 2, .triangle 21 1, .gapLower 3 0]

-- Original cycle b89b6ee8a8fda78dfa02bdd14778f2be6d08f4d32c9389e90551d5d6d348abf1; original global index 14405.
def localCycle00100 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0]

-- Original cycle b9150a60753f21e2f540880c7c6f5a685b19dd00adf313645f04ec61ef268a14; original global index 14442.
def localCycle00101 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 0 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle bbdd2769a76e7bdc61bda66392386acf6ef3bba98de1210ccb8acb5d4ca64832; original global index 14674.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle bd11da19a322d66411d2336a57e58c875abd98e65d1476aa4af0d722817f1aea; original global index 14751.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle bd4b17bf01d1337f05827f9ef4a5210e5c1afba437979d68924b0edd345b2b07; original global index 14766.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c380a57a89469cc0b0dfbc87a47cb666b27f139248cbe770fadefea91aea5886; original global index 15257.
def localCycle00105 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 4, .gapUpper 2 3]

-- Original cycle c494cfff4f8adab3c02a22762f405da40244ec0a71cbe1677de38cca77f19b57; original global index 15330.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle c64815420e4a0735132064ddb2444f084a53657b7c4e19ac4c060ce7152a88d4; original global index 15464.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c703dd567107fedb01ff6d5946e2cf5318bb3995ad00b6d9ececdc93dd4ef154; original global index 15531.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle c8ee35699dae69ddf1e6a91691bef88ff517e276988d5c0e11acd81dc260cd6e; original global index 15693.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .corridorLower 3 6]

-- Original cycle c9319e55c3476d58b73fe1ce457134ffc07d7216e40774fc9e44c731ea3c39df; original global index 15723.
def localCycle00110 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .gapLower 6 2, .triangle 21 1, .gapLower 3 0]

-- Original cycle ca2dffcebca079a1ba67a722dd923d207e33a61c8018af95e7d098b3318c09ab; original global index 15800.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle cae633ba4251933e2f5f98dc4e4d255dc2ccedd4c628a728788f24acae9fbb71; original global index 15854.
def localCycle00112 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle cc7d6cad3de2b9a68fdcef6fd59f1130aae6f3499bacb404cc0c3a283c926af5; original global index 15984.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle d1e3618d6c216e1a8fb7d6ec35a1fdbde7d5d0738470512b847026da3fab354a; original global index 16380.
def localCycle00114 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 4, .gapUpper 2 3]

-- Original cycle d36a18f1258badcbc355c5e6d4dae8c3045eb26606aa5aa01862856792aebdd0; original global index 16491.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle d569a83aff8e7e08455bbf129648b7817bd37ad1c53626f72fce83b01013b18a; original global index 16656.
def localCycle00116 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 5 1]

-- Original cycle d9b99323f6a8a0eedf67cdc19f51b5406b15c2cf3ece9ff762d60272c1572c57; original global index 17008.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Original cycle dafcad7c93edb8479dd3e5a8eac47889a581d66c11b5330783af4dca647c60e3; original global index 17114.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .gapLower 3 0]

-- Original cycle e537361cb619822eac56827c5db6b7d61c2b9f930764cb84c0a25db25815c8a6; original global index 17918.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 32 2, .triangle 33 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle e7f71ba19b97ecd539501a02e5bfc1aa859aca75098a3ae9e48f300729498b40; original global index 18140.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle e8f013c73ba7fd4d5396c0f58eb48e4622a298a9de711ac26cd69e0e9e72b727; original global index 18204.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle ec0fef1f90d6125f6c488a585c3b3443de3ad4f07c6931b6360b3dfb2566e7f7; original global index 18424.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle edae0c4aa47b5a0d2b79fb129f6f9518fa8249b2ed7bcf3e0064a8b66593ab7a; original global index 18557.
def localCycle00123 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle f225f03cfbd36411122ff543dbc060248dab64c811304c6311e34514b600d42a; original global index 18883.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle f22bd7b59bb5a1e4a4e5fb8b026512490585afbc3dc6574fc816d14cb770555e; original global index 18886.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle f306c6d8839795c76d235bc410f86e66858e96880ad538f4fd6461e04ecbef69; original global index 18946.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 2, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle f6ac3edf0a592a3fa9dec4bb6ef342f0f9800e7a0144cac99cc40018f76e9fac; original global index 19245.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f83049219e11cff9f8b40d18fc59e9e4c85628922ace1c9fcb2922fa9401eaf5; original global index 19355.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 0]

-- Original cycle fa3efd54c1446268be71d6b7029b82339cce2ec842bd9d9b94ca7ea588fe6251; original global index 19516.
def localCycle00129 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle fa89a970304877f6518bea67441b3d77088931bbe7a1ba7fce7726b01cb3b2b3; original global index 19545.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .gapLower 4 1, .gapLower 1 2, .gapLower 3 0]

-- Original cycle fb1fe134ceb1190899c3bedc4c460901489e6d850f6e91b35068ae723c602af6; original global index 19603.
def localCycle00131 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle fb530106e08138770e79d6b3ee7cca8e55ee1fafb53a3df2eeece330a9035840; original global index 19614.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle feb5470b1992093c2e6001eb4c57de6b87e4073f4519d5f1c64719384a70a9ea; original global index 19915.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle ffcd02b12386075cf49044efa9df022a4d3893a09f9ee612e8ff3218268ed9ae; original global index 20008.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

def library : Library := fun id => if id < 67 then (if id < 33 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))))) else (if id < 50 then (if id < 41 then (if id < 37 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 45 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))))) else (if id < 58 then (if id < 54 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 62 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))))))) else (if id < 101 then (if id < 84 then (if id < 75 then (if id < 71 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))) else (if id < 79 then (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))))) else (if id < 92 then (if id < 88 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 96 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))))) else (if id < 118 then (if id < 109 then (if id < 105 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))) else (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 113 then (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)))))) else (if id < 126 then (if id < 122 then (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))) else (if id < 130 then (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 1, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 83 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19072)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 89 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19073)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 109 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19074)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 118 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19075)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 109 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19076)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![5, 2, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 4, 3, 6], ![5, 1, 0, 4, 2, 6], ![5, 1, 0, 3, 2, 6], ![4, 3, 1, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 116 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19077)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![5, 2, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 4, 6, 3], ![5, 1, 0, 4, 6, 2], ![5, 1, 0, 3, 2, 6], ![4, 3, 1, 2, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 54 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19078)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 2, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 0, 4, 6, 2], ![5, 1, 0, 3, 6, 2], ![4, 3, 1, 2, 0, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 103 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19079)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 2, 3, 4, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 3, 1, 2, 0, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 87 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19080)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 2, 3, 6, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 3, 1, 2, 0, 6], ![1, 4, 0, 3, 2, 5]], proof := .tail 86 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19081)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 2, 3, 6, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 2, 0, 6], ![4, 1, 0, 3, 2, 5]], proof := .tail 95 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19082)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 2, 6, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 3, 1, 2, 0, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 5 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19083)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 2, 6, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 2, 0, 6], ![4, 1, 3, 0, 2, 5]], proof := .tail 5 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19084)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 2, 6, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 0, 6, 4, 3], ![5, 6, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 57 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19085)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 6, 2, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 3, 1, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 65 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19086)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 6, 2, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 65 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19087)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 6, 2, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 6, 0, 4, 3], ![5, 6, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 50 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19088)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 3, 1, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 123 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19089)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 6, 5, 0, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 3, 1, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19090)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 123 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19091)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 6, 5, 0, 4, 3], ![5, 1, 6, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19092)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 6, 0, 4, 3], ![5, 6, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 2, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 115 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19093)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 6, 5, 0, 4, 3], ![5, 6, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 1, 6, 2, 0], ![4, 3, 1, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19094)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 0, 4, 3], ![5, 6, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 1, 2, 0]], proof := .tail 21 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19095)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 0, 4, 3], ![6, 5, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 34 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19096)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 0, 4, 3], ![6, 5, 1, 0, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 83 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19097)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 0, 4, 3], ![5, 6, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 128 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19098)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 0, 4, 3], ![6, 5, 1, 0, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 118 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19099)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 2, 3, 4, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 0, 4, 3], ![6, 5, 1, 0, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 64 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19100)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 4, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 5, 0, 2, 6], ![1, 3, 4, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 131 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19101)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 4, 6, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 5, 0, 2, 6], ![1, 3, 4, 2, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 4 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19102)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 4, 5, 0, 6, 2], ![1, 3, 5, 0, 6, 2], ![1, 3, 4, 2, 0, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 20 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19103)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 2, 4, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 4, 6, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 0, 2, 6], ![1, 3, 4, 2, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 4 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19104)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 2, 4, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 0, 6, 2], ![1, 3, 4, 2, 0, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 102 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19105)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 6, 0, 2], ![1, 3, 4, 2, 0, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 11 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19106)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 0, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 6, 0, 2], ![1, 3, 4, 2, 0, 6], ![1, 3, 4, 2, 0, 5]], proof := .tail 44 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19107)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 0, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 6, 0, 2], ![1, 3, 4, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 72 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19108)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 5, 6, 0, 2], ![1, 3, 4, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 47 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19109)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 4, 5, 6, 0, 2], ![1, 3, 6, 5, 0, 2], ![1, 3, 6, 4, 2, 0], ![1, 3, 5, 4, 2, 0]], proof := .tail 39 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19110)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 5, 0, 2], ![1, 6, 3, 4, 2, 0], ![1, 5, 3, 4, 2, 0]], proof := .tail 4 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19111)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 5, 0, 2], ![1, 6, 3, 4, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 130 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19112)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 0, 4, 3], ![1, 4, 6, 5, 0, 2], ![1, 3, 6, 5, 0, 2], ![6, 1, 3, 4, 2, 0], ![5, 1, 3, 4, 2, 0]], proof := .tail 4 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19113)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 4, 5, 0, 2], ![1, 6, 3, 5, 0, 2], ![6, 1, 3, 4, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 132 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19114)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 4, 5, 0, 2], ![6, 1, 3, 5, 0, 2], ![6, 1, 3, 4, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 132 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19115)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 0, 4, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 5, 0, 2], ![6, 1, 3, 4, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 41 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19116)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 5, 0, 4, 3], ![6, 1, 4, 5, 0, 2], ![6, 1, 3, 5, 0, 2], ![6, 1, 3, 4, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 41 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19117)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 4, 3, 6], ![1, 5, 4, 0, 2, 6], ![1, 5, 3, 0, 2, 6], ![1, 4, 3, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 107 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19118)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 4, 6, 3], ![1, 5, 4, 0, 6, 2], ![1, 5, 3, 0, 2, 6], ![1, 4, 3, 2, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 98 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19119)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 5, 4, 0, 6, 2], ![1, 5, 3, 0, 6, 2], ![1, 4, 3, 2, 0, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 112 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19120)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 2, 4, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 4, 6, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 0, 2, 6], ![1, 4, 3, 2, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 9 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19121)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 2, 4, 6, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 0, 6, 2], ![1, 4, 3, 2, 0, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 43 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19122)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 6, 0, 2], ![1, 4, 3, 2, 0, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 81 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19123)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 5, 6, 4, 0, 2], ![1, 5, 6, 3, 0, 2], ![1, 4, 3, 2, 0, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 55 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19124)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 0, 4, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 6, 0, 2], ![1, 4, 3, 2, 0, 6], ![1, 3, 4, 2, 0, 5]], proof := .tail 22 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19125)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 0, 4, 3], ![1, 5, 6, 4, 0, 2], ![1, 5, 6, 3, 0, 2], ![1, 4, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 55 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19126)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 0, 4, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 6, 0, 2], ![1, 4, 3, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 117 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19127)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 0, 4, 3], ![1, 5, 6, 4, 0, 2], ![1, 5, 6, 3, 0, 2], ![1, 4, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 123 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19128)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 5, 4, 6, 0, 2], ![1, 5, 3, 6, 0, 2], ![1, 4, 3, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19129)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 5, 6, 4, 0, 2], ![1, 5, 6, 3, 0, 2], ![1, 4, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19130)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 5, 4, 0, 2], ![1, 5, 6, 3, 0, 2], ![1, 4, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 23 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19131)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 5, 4, 0, 2], ![1, 6, 5, 3, 0, 2], ![1, 6, 4, 3, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 97 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19132)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 5, 4, 0, 2], ![1, 6, 5, 3, 0, 2], ![6, 1, 4, 3, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 17 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19133)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 5, 4, 0, 2], ![6, 1, 5, 3, 0, 2], ![6, 1, 4, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 33 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19134)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 0, 4, 3], ![6, 1, 5, 4, 0, 2], ![6, 1, 5, 3, 0, 2], ![6, 1, 4, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 33 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19135)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 5, 0, 4, 3], ![6, 1, 5, 4, 0, 2], ![6, 1, 5, 3, 0, 2], ![6, 1, 4, 3, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 64 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19136)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 0, 4, 3, 6], ![1, 5, 4, 0, 2, 6], ![5, 1, 3, 0, 2, 6], ![4, 1, 3, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 100 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19137)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 0, 4, 6, 3], ![1, 5, 4, 0, 6, 2], ![5, 1, 3, 0, 2, 6], ![4, 1, 3, 2, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 63 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19138)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 5, 4, 0, 6, 2], ![5, 1, 3, 0, 6, 2], ![4, 1, 3, 2, 0, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 26 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19139)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![5, 2, 4, 6, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 0, 4, 6, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 0, 2, 6], ![4, 1, 3, 2, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 30 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19140)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![5, 2, 4, 6, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 0, 6, 2], ![4, 1, 3, 2, 0, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 43 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19141)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 1, 3, 2, 0, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 6 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19142)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 1, 3, 2, 0, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 88 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19143)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 0, 6, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 1, 3, 2, 0, 6], ![4, 1, 3, 0, 2, 5]], proof := .low6 (![3, 32, 48, 19, 52, 24, 113, 126, 38, 51, 10, 75, 15, 12, 25, 67, 75, 80, 91, 66, 75, 61, 101, 75, 14, 74, 28, 93]) }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19144)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 0, 4, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 1, 3, 2, 0, 6], ![1, 3, 4, 2, 0, 5]], proof := .tail 68 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19145)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 0, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 1, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 120 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19146)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 0, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .low6 (![53, 40, 110, 129, 105, 85, 60, 49, 99, 2, 114, 0, 108, 99, 2, 124, 45, 45, 13, 90, 99, 99, 31, 96, 96, 122, 46, 92]) }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19147)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 0, 4, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 1, 3, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 76 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19148)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 0, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 1, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 82 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19149)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 0, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 123 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19150)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 5, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 1, 3, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19151)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 1, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19152)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 5, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 1, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 78 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19153)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 0, 4, 3], ![1, 5, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 1, 3, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19154)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 5, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 1, 6, 3, 2, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 78 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19155)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 5, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 6, 1, 3, 2, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 27 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19156)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 0, 4, 3], ![1, 6, 5, 4, 0, 2], ![6, 5, 1, 3, 0, 2], ![6, 4, 1, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 29 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19157)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 0, 4, 3], ![6, 1, 5, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 121 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19158)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 0, 4, 3], ![6, 1, 5, 4, 0, 2], ![6, 5, 1, 3, 0, 2], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 58 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19159)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 5, 0, 4, 3], ![6, 1, 5, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 118 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19160)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![6, 2, 3, 5, 4, 0], ![6, 1, 5, 0, 4, 3], ![6, 1, 5, 4, 0, 2], ![6, 5, 1, 3, 0, 2], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 64 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19161)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 4, 3, 6], ![5, 1, 4, 0, 2, 6], ![5, 1, 3, 0, 2, 6], ![4, 3, 1, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 69 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19162)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 4, 6, 3], ![5, 1, 4, 0, 6, 2], ![5, 1, 3, 0, 2, 6], ![4, 3, 1, 2, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 59 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19163)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 4, 0, 6, 2], ![5, 1, 3, 0, 6, 2], ![4, 3, 1, 2, 0, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 94 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19164)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![5, 2, 4, 6, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 4, 6, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 0, 2, 6], ![4, 3, 1, 2, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 125 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19165)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![5, 2, 4, 6, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 0, 6, 2], ![4, 3, 1, 2, 0, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 134 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19166)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 3, 1, 2, 0, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 35 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19167)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 3, 1, 2, 0, 6], ![1, 4, 3, 0, 2, 5]], proof := .tail 56 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19168)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 0, 6, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 2, 0, 6], ![4, 1, 3, 0, 2, 5]], proof := .tail 127 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19169)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 0, 6, 4, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 104 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19170)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 0, 4, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 3, 1, 2, 0, 6], ![1, 3, 4, 2, 0, 5]], proof := .tail 8 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19171)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 0, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 3, 1, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 65 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19172)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 6, 0, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 65 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19173)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 6, 0, 4, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 104 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19174)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 0, 4, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 3, 1, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 111 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19175)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 0, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 3, 1, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 73 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19176)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 6, 0, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 1 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19177)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 6, 0, 4, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 2, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 62 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19178)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 6, 5, 0, 4, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 0, 2], ![4, 3, 1, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 42 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19179)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 6, 5, 0, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 0, 2], ![4, 3, 1, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19180)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 5, 3, 6, 4, 0], ![1, 6, 5, 0, 4, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19181)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 5, 6, 3, 4, 0], ![1, 6, 5, 0, 4, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 1, 6, 2, 0], ![4, 3, 1, 5, 2, 0]], proof := .tail 16 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19182)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 0, 4, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 1, 2, 0]], proof := .tail 7 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19183)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 0, 4, 3], ![6, 5, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 36 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19184)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 0, 4, 3], ![6, 5, 1, 4, 0, 2], ![6, 5, 1, 3, 0, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 79 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19185)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 0, 4, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 128 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19186)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 0, 4, 3], ![6, 5, 1, 4, 0, 2], ![5, 6, 1, 3, 0, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 118 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19187)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 0, 4, 3], ![6, 5, 1, 4, 0, 2], ![6, 5, 1, 3, 0, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 64 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19188)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 5, 0, 4, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 5, 0, 2, 6], ![1, 3, 4, 2, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 133 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19189)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 5, 0, 4, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 5, 0, 2, 6], ![1, 3, 4, 2, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 18 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19190)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![5, 2, 4, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 5, 0, 6, 4, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 5, 0, 6, 2], ![1, 3, 4, 2, 0, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 71 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19191)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![5, 2, 4, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 5, 0, 4, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 0, 2, 6], ![1, 3, 4, 2, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 18 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19192)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![5, 2, 4, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 5, 0, 6, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 0, 6, 2], ![1, 3, 4, 2, 0, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 37 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19193)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![5, 2, 6, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 5, 0, 6, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 6, 0, 2], ![1, 3, 4, 2, 0, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 18 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19194)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![5, 6, 2, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 5, 6, 0, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 6, 0, 2], ![1, 3, 4, 2, 0, 6], ![1, 3, 4, 2, 0, 5]], proof := .tail 119 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19195)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 5, 6, 0, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 6, 0, 2], ![1, 3, 4, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 106 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19196)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 6, 0, 2], ![1, 3, 4, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 84 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19197)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 6, 5, 0, 2], ![1, 3, 6, 4, 2, 0], ![1, 3, 5, 4, 2, 0]], proof := .tail 77 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19198)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 5, 2, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 5, 0, 4, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 6, 5, 0, 2], ![1, 6, 3, 4, 2, 0], ![1, 5, 3, 4, 2, 0]], proof := .tail 70 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19199)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then
  (if offset < 32 then
  (if offset < 16 then
  (if offset < 8 then
  (if offset < 4 then
  (if offset < 2 then
  (if offset < 1 then
  (namedLeaf000) else
  (namedLeaf001)) else
  (if offset < 3 then
  (namedLeaf002) else
  (namedLeaf003))) else
  (if offset < 6 then
  (if offset < 5 then
  (namedLeaf004) else
  (namedLeaf005)) else
  (if offset < 7 then
  (namedLeaf006) else
  (namedLeaf007)))) else
  (if offset < 12 then
  (if offset < 10 then
  (if offset < 9 then
  (namedLeaf008) else
  (namedLeaf009)) else
  (if offset < 11 then
  (namedLeaf010) else
  (namedLeaf011))) else
  (if offset < 14 then
  (if offset < 13 then
  (namedLeaf012) else
  (namedLeaf013)) else
  (if offset < 15 then
  (namedLeaf014) else
  (namedLeaf015))))) else
  (if offset < 24 then
  (if offset < 20 then
  (if offset < 18 then
  (if offset < 17 then
  (namedLeaf016) else
  (namedLeaf017)) else
  (if offset < 19 then
  (namedLeaf018) else
  (namedLeaf019))) else
  (if offset < 22 then
  (if offset < 21 then
  (namedLeaf020) else
  (namedLeaf021)) else
  (if offset < 23 then
  (namedLeaf022) else
  (namedLeaf023)))) else
  (if offset < 28 then
  (if offset < 26 then
  (if offset < 25 then
  (namedLeaf024) else
  (namedLeaf025)) else
  (if offset < 27 then
  (namedLeaf026) else
  (namedLeaf027))) else
  (if offset < 30 then
  (if offset < 29 then
  (namedLeaf028) else
  (namedLeaf029)) else
  (if offset < 31 then
  (namedLeaf030) else
  (namedLeaf031)))))) else
  (if offset < 48 then
  (if offset < 40 then
  (if offset < 36 then
  (if offset < 34 then
  (if offset < 33 then
  (namedLeaf032) else
  (namedLeaf033)) else
  (if offset < 35 then
  (namedLeaf034) else
  (namedLeaf035))) else
  (if offset < 38 then
  (if offset < 37 then
  (namedLeaf036) else
  (namedLeaf037)) else
  (if offset < 39 then
  (namedLeaf038) else
  (namedLeaf039)))) else
  (if offset < 44 then
  (if offset < 42 then
  (if offset < 41 then
  (namedLeaf040) else
  (namedLeaf041)) else
  (if offset < 43 then
  (namedLeaf042) else
  (namedLeaf043))) else
  (if offset < 46 then
  (if offset < 45 then
  (namedLeaf044) else
  (namedLeaf045)) else
  (if offset < 47 then
  (namedLeaf046) else
  (namedLeaf047))))) else
  (if offset < 56 then
  (if offset < 52 then
  (if offset < 50 then
  (if offset < 49 then
  (namedLeaf048) else
  (namedLeaf049)) else
  (if offset < 51 then
  (namedLeaf050) else
  (namedLeaf051))) else
  (if offset < 54 then
  (if offset < 53 then
  (namedLeaf052) else
  (namedLeaf053)) else
  (if offset < 55 then
  (namedLeaf054) else
  (namedLeaf055)))) else
  (if offset < 60 then
  (if offset < 58 then
  (if offset < 57 then
  (namedLeaf056) else
  (namedLeaf057)) else
  (if offset < 59 then
  (namedLeaf058) else
  (namedLeaf059))) else
  (if offset < 62 then
  (if offset < 61 then
  (namedLeaf060) else
  (namedLeaf061)) else
  (if offset < 63 then
  (namedLeaf062) else
  (namedLeaf063))))))) else
  (if offset < 96 then
  (if offset < 80 then
  (if offset < 72 then
  (if offset < 68 then
  (if offset < 66 then
  (if offset < 65 then
  (namedLeaf064) else
  (namedLeaf065)) else
  (if offset < 67 then
  (namedLeaf066) else
  (namedLeaf067))) else
  (if offset < 70 then
  (if offset < 69 then
  (namedLeaf068) else
  (namedLeaf069)) else
  (if offset < 71 then
  (namedLeaf070) else
  (namedLeaf071)))) else
  (if offset < 76 then
  (if offset < 74 then
  (if offset < 73 then
  (namedLeaf072) else
  (namedLeaf073)) else
  (if offset < 75 then
  (namedLeaf074) else
  (namedLeaf075))) else
  (if offset < 78 then
  (if offset < 77 then
  (namedLeaf076) else
  (namedLeaf077)) else
  (if offset < 79 then
  (namedLeaf078) else
  (namedLeaf079))))) else
  (if offset < 88 then
  (if offset < 84 then
  (if offset < 82 then
  (if offset < 81 then
  (namedLeaf080) else
  (namedLeaf081)) else
  (if offset < 83 then
  (namedLeaf082) else
  (namedLeaf083))) else
  (if offset < 86 then
  (if offset < 85 then
  (namedLeaf084) else
  (namedLeaf085)) else
  (if offset < 87 then
  (namedLeaf086) else
  (namedLeaf087)))) else
  (if offset < 92 then
  (if offset < 90 then
  (if offset < 89 then
  (namedLeaf088) else
  (namedLeaf089)) else
  (if offset < 91 then
  (namedLeaf090) else
  (namedLeaf091))) else
  (if offset < 94 then
  (if offset < 93 then
  (namedLeaf092) else
  (namedLeaf093)) else
  (if offset < 95 then
  (namedLeaf094) else
  (namedLeaf095)))))) else
  (if offset < 112 then
  (if offset < 104 then
  (if offset < 100 then
  (if offset < 98 then
  (if offset < 97 then
  (namedLeaf096) else
  (namedLeaf097)) else
  (if offset < 99 then
  (namedLeaf098) else
  (namedLeaf099))) else
  (if offset < 102 then
  (if offset < 101 then
  (namedLeaf100) else
  (namedLeaf101)) else
  (if offset < 103 then
  (namedLeaf102) else
  (namedLeaf103)))) else
  (if offset < 108 then
  (if offset < 106 then
  (if offset < 105 then
  (namedLeaf104) else
  (namedLeaf105)) else
  (if offset < 107 then
  (namedLeaf106) else
  (namedLeaf107))) else
  (if offset < 110 then
  (if offset < 109 then
  (namedLeaf108) else
  (namedLeaf109)) else
  (if offset < 111 then
  (namedLeaf110) else
  (namedLeaf111))))) else
  (if offset < 120 then
  (if offset < 116 then
  (if offset < 114 then
  (if offset < 113 then
  (namedLeaf112) else
  (namedLeaf113)) else
  (if offset < 115 then
  (namedLeaf114) else
  (namedLeaf115))) else
  (if offset < 118 then
  (if offset < 117 then
  (namedLeaf116) else
  (namedLeaf117)) else
  (if offset < 119 then
  (namedLeaf118) else
  (namedLeaf119)))) else
  (if offset < 124 then
  (if offset < 122 then
  (if offset < 121 then
  (namedLeaf120) else
  (namedLeaf121)) else
  (if offset < 123 then
  (namedLeaf122) else
  (namedLeaf123))) else
  (if offset < 126 then
  (if offset < 125 then
  (namedLeaf124) else
  (namedLeaf125)) else
  (if offset < 127 then
  (namedLeaf126) else
  (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (19072 + j.val))) (lookup j.val) = true := by
  have hjbound : j.val < 128 := j.isLt
  by_cases h64 : j.val < 64
  · by_cases h32 : j.val < 32
    · by_cases h16 : j.val < 16
      · by_cases h8 : j.val < 8
        · by_cases h4 : j.val < 4
          · by_cases h2 : j.val < 2
            · by_cases h1 : j.val < 1
              · have hj : j = ⟨0, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 0
                  omega
                subst j
                exact namedLeaf000_checked
              · have hj : j = ⟨1, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 1
                  omega
                subst j
                exact namedLeaf001_checked
            · by_cases h3 : j.val < 3
              · have hj : j = ⟨2, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 2
                  omega
                subst j
                exact namedLeaf002_checked
              · have hj : j = ⟨3, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 3
                  omega
                subst j
                exact namedLeaf003_checked
          · by_cases h6 : j.val < 6
            · by_cases h5 : j.val < 5
              · have hj : j = ⟨4, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 4
                  omega
                subst j
                exact namedLeaf004_checked
              · have hj : j = ⟨5, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 5
                  omega
                subst j
                exact namedLeaf005_checked
            · by_cases h7 : j.val < 7
              · have hj : j = ⟨6, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 6
                  omega
                subst j
                exact namedLeaf006_checked
              · have hj : j = ⟨7, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 7
                  omega
                subst j
                exact namedLeaf007_checked
        · by_cases h12 : j.val < 12
          · by_cases h10 : j.val < 10
            · by_cases h9 : j.val < 9
              · have hj : j = ⟨8, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 8
                  omega
                subst j
                exact namedLeaf008_checked
              · have hj : j = ⟨9, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 9
                  omega
                subst j
                exact namedLeaf009_checked
            · by_cases h11 : j.val < 11
              · have hj : j = ⟨10, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 10
                  omega
                subst j
                exact namedLeaf010_checked
              · have hj : j = ⟨11, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 11
                  omega
                subst j
                exact namedLeaf011_checked
          · by_cases h14 : j.val < 14
            · by_cases h13 : j.val < 13
              · have hj : j = ⟨12, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 12
                  omega
                subst j
                exact namedLeaf012_checked
              · have hj : j = ⟨13, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 13
                  omega
                subst j
                exact namedLeaf013_checked
            · by_cases h15 : j.val < 15
              · have hj : j = ⟨14, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 14
                  omega
                subst j
                exact namedLeaf014_checked
              · have hj : j = ⟨15, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 15
                  omega
                subst j
                exact namedLeaf015_checked
      · by_cases h24 : j.val < 24
        · by_cases h20 : j.val < 20
          · by_cases h18 : j.val < 18
            · by_cases h17 : j.val < 17
              · have hj : j = ⟨16, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 16
                  omega
                subst j
                exact namedLeaf016_checked
              · have hj : j = ⟨17, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 17
                  omega
                subst j
                exact namedLeaf017_checked
            · by_cases h19 : j.val < 19
              · have hj : j = ⟨18, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 18
                  omega
                subst j
                exact namedLeaf018_checked
              · have hj : j = ⟨19, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 19
                  omega
                subst j
                exact namedLeaf019_checked
          · by_cases h22 : j.val < 22
            · by_cases h21 : j.val < 21
              · have hj : j = ⟨20, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 20
                  omega
                subst j
                exact namedLeaf020_checked
              · have hj : j = ⟨21, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 21
                  omega
                subst j
                exact namedLeaf021_checked
            · by_cases h23 : j.val < 23
              · have hj : j = ⟨22, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 22
                  omega
                subst j
                exact namedLeaf022_checked
              · have hj : j = ⟨23, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 23
                  omega
                subst j
                exact namedLeaf023_checked
        · by_cases h28 : j.val < 28
          · by_cases h26 : j.val < 26
            · by_cases h25 : j.val < 25
              · have hj : j = ⟨24, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 24
                  omega
                subst j
                exact namedLeaf024_checked
              · have hj : j = ⟨25, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 25
                  omega
                subst j
                exact namedLeaf025_checked
            · by_cases h27 : j.val < 27
              · have hj : j = ⟨26, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 26
                  omega
                subst j
                exact namedLeaf026_checked
              · have hj : j = ⟨27, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 27
                  omega
                subst j
                exact namedLeaf027_checked
          · by_cases h30 : j.val < 30
            · by_cases h29 : j.val < 29
              · have hj : j = ⟨28, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 28
                  omega
                subst j
                exact namedLeaf028_checked
              · have hj : j = ⟨29, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 29
                  omega
                subst j
                exact namedLeaf029_checked
            · by_cases h31 : j.val < 31
              · have hj : j = ⟨30, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 30
                  omega
                subst j
                exact namedLeaf030_checked
              · have hj : j = ⟨31, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 31
                  omega
                subst j
                exact namedLeaf031_checked
    · by_cases h48 : j.val < 48
      · by_cases h40 : j.val < 40
        · by_cases h36 : j.val < 36
          · by_cases h34 : j.val < 34
            · by_cases h33 : j.val < 33
              · have hj : j = ⟨32, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 32
                  omega
                subst j
                exact namedLeaf032_checked
              · have hj : j = ⟨33, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 33
                  omega
                subst j
                exact namedLeaf033_checked
            · by_cases h35 : j.val < 35
              · have hj : j = ⟨34, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 34
                  omega
                subst j
                exact namedLeaf034_checked
              · have hj : j = ⟨35, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 35
                  omega
                subst j
                exact namedLeaf035_checked
          · by_cases h38 : j.val < 38
            · by_cases h37 : j.val < 37
              · have hj : j = ⟨36, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 36
                  omega
                subst j
                exact namedLeaf036_checked
              · have hj : j = ⟨37, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 37
                  omega
                subst j
                exact namedLeaf037_checked
            · by_cases h39 : j.val < 39
              · have hj : j = ⟨38, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 38
                  omega
                subst j
                exact namedLeaf038_checked
              · have hj : j = ⟨39, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 39
                  omega
                subst j
                exact namedLeaf039_checked
        · by_cases h44 : j.val < 44
          · by_cases h42 : j.val < 42
            · by_cases h41 : j.val < 41
              · have hj : j = ⟨40, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 40
                  omega
                subst j
                exact namedLeaf040_checked
              · have hj : j = ⟨41, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 41
                  omega
                subst j
                exact namedLeaf041_checked
            · by_cases h43 : j.val < 43
              · have hj : j = ⟨42, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 42
                  omega
                subst j
                exact namedLeaf042_checked
              · have hj : j = ⟨43, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 43
                  omega
                subst j
                exact namedLeaf043_checked
          · by_cases h46 : j.val < 46
            · by_cases h45 : j.val < 45
              · have hj : j = ⟨44, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 44
                  omega
                subst j
                exact namedLeaf044_checked
              · have hj : j = ⟨45, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 45
                  omega
                subst j
                exact namedLeaf045_checked
            · by_cases h47 : j.val < 47
              · have hj : j = ⟨46, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 46
                  omega
                subst j
                exact namedLeaf046_checked
              · have hj : j = ⟨47, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 47
                  omega
                subst j
                exact namedLeaf047_checked
      · by_cases h56 : j.val < 56
        · by_cases h52 : j.val < 52
          · by_cases h50 : j.val < 50
            · by_cases h49 : j.val < 49
              · have hj : j = ⟨48, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 48
                  omega
                subst j
                exact namedLeaf048_checked
              · have hj : j = ⟨49, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 49
                  omega
                subst j
                exact namedLeaf049_checked
            · by_cases h51 : j.val < 51
              · have hj : j = ⟨50, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 50
                  omega
                subst j
                exact namedLeaf050_checked
              · have hj : j = ⟨51, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 51
                  omega
                subst j
                exact namedLeaf051_checked
          · by_cases h54 : j.val < 54
            · by_cases h53 : j.val < 53
              · have hj : j = ⟨52, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 52
                  omega
                subst j
                exact namedLeaf052_checked
              · have hj : j = ⟨53, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 53
                  omega
                subst j
                exact namedLeaf053_checked
            · by_cases h55 : j.val < 55
              · have hj : j = ⟨54, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 54
                  omega
                subst j
                exact namedLeaf054_checked
              · have hj : j = ⟨55, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 55
                  omega
                subst j
                exact namedLeaf055_checked
        · by_cases h60 : j.val < 60
          · by_cases h58 : j.val < 58
            · by_cases h57 : j.val < 57
              · have hj : j = ⟨56, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 56
                  omega
                subst j
                exact namedLeaf056_checked
              · have hj : j = ⟨57, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 57
                  omega
                subst j
                exact namedLeaf057_checked
            · by_cases h59 : j.val < 59
              · have hj : j = ⟨58, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 58
                  omega
                subst j
                exact namedLeaf058_checked
              · have hj : j = ⟨59, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 59
                  omega
                subst j
                exact namedLeaf059_checked
          · by_cases h62 : j.val < 62
            · by_cases h61 : j.val < 61
              · have hj : j = ⟨60, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 60
                  omega
                subst j
                exact namedLeaf060_checked
              · have hj : j = ⟨61, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 61
                  omega
                subst j
                exact namedLeaf061_checked
            · by_cases h63 : j.val < 63
              · have hj : j = ⟨62, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 62
                  omega
                subst j
                exact namedLeaf062_checked
              · have hj : j = ⟨63, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 63
                  omega
                subst j
                exact namedLeaf063_checked
  · by_cases h96 : j.val < 96
    · by_cases h80 : j.val < 80
      · by_cases h72 : j.val < 72
        · by_cases h68 : j.val < 68
          · by_cases h66 : j.val < 66
            · by_cases h65 : j.val < 65
              · have hj : j = ⟨64, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 64
                  omega
                subst j
                exact namedLeaf064_checked
              · have hj : j = ⟨65, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 65
                  omega
                subst j
                exact namedLeaf065_checked
            · by_cases h67 : j.val < 67
              · have hj : j = ⟨66, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 66
                  omega
                subst j
                exact namedLeaf066_checked
              · have hj : j = ⟨67, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 67
                  omega
                subst j
                exact namedLeaf067_checked
          · by_cases h70 : j.val < 70
            · by_cases h69 : j.val < 69
              · have hj : j = ⟨68, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 68
                  omega
                subst j
                exact namedLeaf068_checked
              · have hj : j = ⟨69, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 69
                  omega
                subst j
                exact namedLeaf069_checked
            · by_cases h71 : j.val < 71
              · have hj : j = ⟨70, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 70
                  omega
                subst j
                exact namedLeaf070_checked
              · have hj : j = ⟨71, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 71
                  omega
                subst j
                exact namedLeaf071_checked
        · by_cases h76 : j.val < 76
          · by_cases h74 : j.val < 74
            · by_cases h73 : j.val < 73
              · have hj : j = ⟨72, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 72
                  omega
                subst j
                exact namedLeaf072_checked
              · have hj : j = ⟨73, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 73
                  omega
                subst j
                exact namedLeaf073_checked
            · by_cases h75 : j.val < 75
              · have hj : j = ⟨74, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 74
                  omega
                subst j
                exact namedLeaf074_checked
              · have hj : j = ⟨75, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 75
                  omega
                subst j
                exact namedLeaf075_checked
          · by_cases h78 : j.val < 78
            · by_cases h77 : j.val < 77
              · have hj : j = ⟨76, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 76
                  omega
                subst j
                exact namedLeaf076_checked
              · have hj : j = ⟨77, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 77
                  omega
                subst j
                exact namedLeaf077_checked
            · by_cases h79 : j.val < 79
              · have hj : j = ⟨78, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 78
                  omega
                subst j
                exact namedLeaf078_checked
              · have hj : j = ⟨79, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 79
                  omega
                subst j
                exact namedLeaf079_checked
      · by_cases h88 : j.val < 88
        · by_cases h84 : j.val < 84
          · by_cases h82 : j.val < 82
            · by_cases h81 : j.val < 81
              · have hj : j = ⟨80, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 80
                  omega
                subst j
                exact namedLeaf080_checked
              · have hj : j = ⟨81, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 81
                  omega
                subst j
                exact namedLeaf081_checked
            · by_cases h83 : j.val < 83
              · have hj : j = ⟨82, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 82
                  omega
                subst j
                exact namedLeaf082_checked
              · have hj : j = ⟨83, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 83
                  omega
                subst j
                exact namedLeaf083_checked
          · by_cases h86 : j.val < 86
            · by_cases h85 : j.val < 85
              · have hj : j = ⟨84, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 84
                  omega
                subst j
                exact namedLeaf084_checked
              · have hj : j = ⟨85, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 85
                  omega
                subst j
                exact namedLeaf085_checked
            · by_cases h87 : j.val < 87
              · have hj : j = ⟨86, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 86
                  omega
                subst j
                exact namedLeaf086_checked
              · have hj : j = ⟨87, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 87
                  omega
                subst j
                exact namedLeaf087_checked
        · by_cases h92 : j.val < 92
          · by_cases h90 : j.val < 90
            · by_cases h89 : j.val < 89
              · have hj : j = ⟨88, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 88
                  omega
                subst j
                exact namedLeaf088_checked
              · have hj : j = ⟨89, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 89
                  omega
                subst j
                exact namedLeaf089_checked
            · by_cases h91 : j.val < 91
              · have hj : j = ⟨90, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 90
                  omega
                subst j
                exact namedLeaf090_checked
              · have hj : j = ⟨91, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 91
                  omega
                subst j
                exact namedLeaf091_checked
          · by_cases h94 : j.val < 94
            · by_cases h93 : j.val < 93
              · have hj : j = ⟨92, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 92
                  omega
                subst j
                exact namedLeaf092_checked
              · have hj : j = ⟨93, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 93
                  omega
                subst j
                exact namedLeaf093_checked
            · by_cases h95 : j.val < 95
              · have hj : j = ⟨94, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 94
                  omega
                subst j
                exact namedLeaf094_checked
              · have hj : j = ⟨95, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 95
                  omega
                subst j
                exact namedLeaf095_checked
    · by_cases h112 : j.val < 112
      · by_cases h104 : j.val < 104
        · by_cases h100 : j.val < 100
          · by_cases h98 : j.val < 98
            · by_cases h97 : j.val < 97
              · have hj : j = ⟨96, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 96
                  omega
                subst j
                exact namedLeaf096_checked
              · have hj : j = ⟨97, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 97
                  omega
                subst j
                exact namedLeaf097_checked
            · by_cases h99 : j.val < 99
              · have hj : j = ⟨98, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 98
                  omega
                subst j
                exact namedLeaf098_checked
              · have hj : j = ⟨99, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 99
                  omega
                subst j
                exact namedLeaf099_checked
          · by_cases h102 : j.val < 102
            · by_cases h101 : j.val < 101
              · have hj : j = ⟨100, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 100
                  omega
                subst j
                exact namedLeaf100_checked
              · have hj : j = ⟨101, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 101
                  omega
                subst j
                exact namedLeaf101_checked
            · by_cases h103 : j.val < 103
              · have hj : j = ⟨102, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 102
                  omega
                subst j
                exact namedLeaf102_checked
              · have hj : j = ⟨103, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 103
                  omega
                subst j
                exact namedLeaf103_checked
        · by_cases h108 : j.val < 108
          · by_cases h106 : j.val < 106
            · by_cases h105 : j.val < 105
              · have hj : j = ⟨104, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 104
                  omega
                subst j
                exact namedLeaf104_checked
              · have hj : j = ⟨105, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 105
                  omega
                subst j
                exact namedLeaf105_checked
            · by_cases h107 : j.val < 107
              · have hj : j = ⟨106, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 106
                  omega
                subst j
                exact namedLeaf106_checked
              · have hj : j = ⟨107, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 107
                  omega
                subst j
                exact namedLeaf107_checked
          · by_cases h110 : j.val < 110
            · by_cases h109 : j.val < 109
              · have hj : j = ⟨108, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 108
                  omega
                subst j
                exact namedLeaf108_checked
              · have hj : j = ⟨109, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 109
                  omega
                subst j
                exact namedLeaf109_checked
            · by_cases h111 : j.val < 111
              · have hj : j = ⟨110, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 110
                  omega
                subst j
                exact namedLeaf110_checked
              · have hj : j = ⟨111, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 111
                  omega
                subst j
                exact namedLeaf111_checked
      · by_cases h120 : j.val < 120
        · by_cases h116 : j.val < 116
          · by_cases h114 : j.val < 114
            · by_cases h113 : j.val < 113
              · have hj : j = ⟨112, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 112
                  omega
                subst j
                exact namedLeaf112_checked
              · have hj : j = ⟨113, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 113
                  omega
                subst j
                exact namedLeaf113_checked
            · by_cases h115 : j.val < 115
              · have hj : j = ⟨114, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 114
                  omega
                subst j
                exact namedLeaf114_checked
              · have hj : j = ⟨115, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 115
                  omega
                subst j
                exact namedLeaf115_checked
          · by_cases h118 : j.val < 118
            · by_cases h117 : j.val < 117
              · have hj : j = ⟨116, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 116
                  omega
                subst j
                exact namedLeaf116_checked
              · have hj : j = ⟨117, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 117
                  omega
                subst j
                exact namedLeaf117_checked
            · by_cases h119 : j.val < 119
              · have hj : j = ⟨118, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 118
                  omega
                subst j
                exact namedLeaf118_checked
              · have hj : j = ⟨119, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 119
                  omega
                subst j
                exact namedLeaf119_checked
        · by_cases h124 : j.val < 124
          · by_cases h122 : j.val < 122
            · by_cases h121 : j.val < 121
              · have hj : j = ⟨120, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 120
                  omega
                subst j
                exact namedLeaf120_checked
              · have hj : j = ⟨121, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 121
                  omega
                subst j
                exact namedLeaf121_checked
            · by_cases h123 : j.val < 123
              · have hj : j = ⟨122, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 122
                  omega
                subst j
                exact namedLeaf122_checked
              · have hj : j = ⟨123, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 123
                  omega
                subst j
                exact namedLeaf123_checked
          · by_cases h126 : j.val < 126
            · by_cases h125 : j.val < 125
              · have hj : j = ⟨124, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 124
                  omega
                subst j
                exact namedLeaf124_checked
              · have hj : j = ⟨125, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 125
                  omega
                subst j
                exact namedLeaf125_checked
            · by_cases h127 : j.val < 127
              · have hj : j = ⟨126, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 126
                  omega
                subst j
                exact namedLeaf126_checked
              · have hj : j = ⟨127, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 127
                  omega
                subst j
                exact namedLeaf127_checked

theorem correct (id : Fin 24698) (hlow : 19072 ≤ id.val) (hhigh : id.val < 19200) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 19072)) = true := by
  let j : Fin 128 := ⟨id.val - 19072, by omega⟩
  have hsum : 19072 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (19072 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard149
