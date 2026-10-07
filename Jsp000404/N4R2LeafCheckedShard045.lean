import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard045
open N4R2RowDataReplay

-- Original cycle 00b7be19c171eddb91bb58591869ec5c2df331c1f89943e70abea73741a0ebd8; original global index 63.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

-- Original cycle 016cc2972c67431fcd8174393720168ae65676ebbc6280275a4d48f6cc66e3ae; original global index 116.
def localCycle00001 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 3 3, .gapLower 4 2, .gapUpper 2 3]

-- Original cycle 023b5d069339680d86db3a39e8552691fed95bbae485795a9af005a7b171d632; original global index 177.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 2, .triangle 5 0, .triangle 26 0, .gapLower 5 0]

-- Original cycle 031518f99ba55e3ba6a59af72b99213ecdfa3a2c4f725feac8d23acf00be293c; original global index 251.
def localCycle00003 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 4, .triangle 9 0, .triangle 25 2, .gapUpper 2 3]

-- Original cycle 075975521197bdba8f61c5bb608c822888134f1565650052f1f609f037016a46; original global index 603.
def localCycle00004 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 09dd667c087ed61b6eed7fb1bdcbabddbce0e53468171a69a0f7a9dab7956c8e; original global index 794.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 11 1, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 09e8c47278a18a862584209f72ac828f3fac984cb22d6ee8016d96b5deaf6f2a; original global index 798.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 2, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 09ea70b78d11b13452d8d56addb06c6ca4b4405c4c759beb05dd936746b0076b; original global index 799.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 0a0fb2ef472d955e887940a4b8f1dfd8cb50f2d58a65cce189cb86c7fafb7a48; original global index 812.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .gapLower 5 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 0adc41e78b966296427eeb400622a2066d0d240669c1fd30111fa5dc27d17120; original global index 864.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 0b4bee06879f506dbfc77bd714b0304e2fe1428bad88a65127f7563eda9fe928; original global index 907.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

-- Original cycle 0bdbab20a5f0d413da43306a59a621625443ffe6c1d06b524eb44f8b572d46dc; original global index 943.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 0c20f7c70c051720235a9c7bbe8638850095e131e39a73ad5f54a2513eefc262; original global index 960.
def localCycle00012 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 3, .distance 0 5, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 11 1, .gapLower 0 3, .corridorLower 0 5]

-- Original cycle 0c4ac887bb3b6f0ae1d94408d3f667f8396046243513759394a6ba43b014f1c1; original global index 972.
def localCycle00013 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .gapLower 3 3, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 0d5360159b74d8f4e133cbcf4751e1750fa38039f3466a76fbbdbfa813629bc9; original global index 1055.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0d8b221b5708f5b35ad975ef4f0c6426828e59276258982e0c5e12ecf6959822; original global index 1071.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 11a937b8517cbbe238910e3d6f9fcad9cc2fa58ecd16a5b835bb5769170d7eaf; original global index 1410.
def localCycle00016 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -3, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 11 0, .gapLower 0 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 12f72cc6d30097e191014f8363477bf290f02c4152941b30b8719cc28cd8d6ed; original global index 1496.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 131f2985c89d090fbce3a276628dd346b328933668978127cba1c2ebb0f3d33b; original global index 1512.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 1364f9abbd5fb48e414e04dd3656dd1c5b7cd463ea2ee5c56f29dd734c3fed71; original global index 1528.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 0, .distance 0 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, -2, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 0, .gapLower 0 6, .gapLower 0 5, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 13f614a76b605736a170c3fed49868a881cabfd800dfb18aa47d51012408d483; original global index 1575.
def localCycle00020 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 16ccb0dfb672de867e0c186f217996cd789d9c6faf4f076cf490b5606cdb1379; original global index 1791.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .gapLower 5 3, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 1838cc6bfad2c0b2eb83fd6f3a00ac0c0fba973f8d6c7be7f534e2aa1e8946aa; original global index 1893.
def localCycle00022 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .triangle 10 0, .gapLower 0 1]

-- Original cycle 1b3ee3dd838f647ea4d295f5411d93df27d48e33aa9caf60f2ad4d3768cb5038; original global index 2111.
def localCycle00023 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .triangle 7 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 1b947741b2826b7f0e03c86889a13959691d9f5f3f2e3798482be6f309d256bb; original global index 2129.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 2, .gapLower 5 3, .triangle 28 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 1b98d25476f310b0111a8ca7a75a4a078e3cae4a2e8af89683b38cf09e344e46; original global index 2134.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 3, .gapLower 5 2, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1d06efaebd49b765f7c93e2857f11dbf752a7c2c91c5dd81cd79695db0319ac7; original global index 2237.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 1d68f29b4cc4899c52d50a67a57c84851249134532cf2799d2b1e5d87e75f60d; original global index 2264.
def localCycle00027 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .triangle 9 2, .gapLower 0 2, .gapLower 5 3, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 1e9779630862a134eb28612ba8c610194eb053d51eba8dca6fe5abac071770c5; original global index 2347.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 1f6cfcc815e07281d5d18f90fbce603be31113f5b2ab4c4d312b9bf1445b77e5; original global index 2413.
def localCycle00029 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .gapLower 4 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 209bf5bf20c74584919b7ddd916b966b44caa8f08f4f364411170e9b6624ec41; original global index 2501.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 210494c3bc1db1ecf30e558cc4aa5f3e4c8f5fec3a157a4383c4e0fa9e2f4eb9; original global index 2533.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 21f252e9e2273ab20e168ed23c07d1fdf0903597cda6c15ddd593317bad6b726; original global index 2598.
def localCycle00032 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .gapLower 0 3, .gapLower 4 3, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 241eb5b62fed0e9e3bed4c1517d40c928f4bc0ec92d5ba3c8a3421d80d54db9d; original global index 2767.
def localCycle00033 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Original cycle 243a1d432f1c3f88b4aa0f25086fbef5ebedcef62e48fdd36f5adfeeef794d16; original global index 2778.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 25099654e47d2bbead5ed9816b7263354b129c08872545e1525a4529154dc2d2; original global index 2845.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![-2, 0, -2, 2, 2, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, true, true, false] }
  origin := ![.gapLower 0 4, .triangle 9 2, .gapLower 0 2, .gapUpper 5 4, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0]

-- Original cycle 2700b5359d5c4123944df0a45b1872f85df0d6614faba04213e4811eac76b74c; original global index 2990.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .triangle 10 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 271f0397601996982c4d25491800f77c58797905d03ad9909bf49b4503a2cd68; original global index 2997.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 5]

-- Original cycle 2a2f023d6d8216dc1c297fb4847f0e90e300747b135494acf7747b928c701a97; original global index 3215.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

-- Original cycle 2acbbca85f966bf1236e15b908d687e7e48adc10766c0571e4a792f8ec4343c0; original global index 3262.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2bea83f7df91a416bc60472a77ec16ca4561d4f5d0c1a6d451203a6d62bf5592; original global index 3360.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 2c2aecd04f2b0dc48adb8828a08ac49964f4e7b562508c9b7f1e4344b42e3124; original global index 3379.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2e9d6dd3601f3cdfac85ba407a4c3bce965c32c414ceeffcd02e6b28d2cc2da4; original global index 3561.
def localCycle00042 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 2ea9e3cbdb43455ff83a2d0ec065a3501e74514b8e13bfb5580afbe84239e6cb; original global index 3565.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 2eaa423714c5a521a3145b45d9362e25dc14d1c3441a1f109067ed6a38c5c802; original global index 3566.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![-2, -2, 2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapUpper 5 4, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 11 0]

-- Original cycle 327477f7be36975050e906993bfdf0a712cfa86b3ee5e14beb53cfe248327e36; original global index 3856.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .gapLower 4 3, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 32d08bd6f7d2ab9183b236cd3b92e1d51468736a09a171f7004d8edd49c0b828; original global index 3892.
def localCycle00046 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 3, .gapLower 5 3, .gapLower 0 2]

-- Original cycle 344a101d62fb8d8bded34fdf8fa52e17746c3d19b2eb24511b0ead553dd0de06; original global index 4007.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 3502556a587709230c5205dd3378f942f8c3923e4b63afe144eed9b4e142e733; original global index 4056.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .gapUpper 2 5]

-- Original cycle 36578b849789d929f8fbf3edfcc0fe5556377fa91d7eaf0f2b65542581b3d253; original global index 4168.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, 0, 0, -3, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 399de4118e0153af67c057438c3e689712c5a5770291940c0b7e9eeb9d0df7ac; original global index 4444.
def localCycle00050 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 3bf3f608741409aa40a5730953a3be5d1574adc3f7d7bedd77ff3505154c807d; original global index 4646.
def localCycle00051 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 3, .gapLower 5 3, .gapLower 0 2]

-- Original cycle 3d07b508a58beb366838666841a3147c670263deee6ffbebe4d20b244ff74694; original global index 4728.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 3d981b98f06b91bb6402b5e6d5dfacd484450a87b0a5e7e00ecb1cfa0a1769e2; original global index 4768.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 3e36735a91799475110744e7328e93d11aaa1438cea1aa49ced6a95d22bcbba8; original global index 4816.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

-- Original cycle 3f6c25bb12887abdeeaef141b85949dccc16e56ad38134bbe1cbcfc77339d1da; original global index 4899.
def localCycle00055 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 5, .distance 0 4, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 14 1, .gapLower 0 2, .corridorLower 0 4]

-- Original cycle 42a9e4de31121ff103c753e84bff9734a72b5933dbc562c19f15c427092190a8; original global index 5133.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 42b3a37f2ddec00812874333648258fb639d6358df2d1af224fbcdec912bf039; original global index 5137.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 14 0, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 42f657aae852cee5a107359ba4734add1cd2e3e35be6dee14df6a5666da39628; original global index 5163.
def localCycle00058 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 42f70301323478230d68a4b214d9ac58316c5547e1bff0d82e5d50c1c5858c9e; original global index 5164.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 2, .gapLower 5 3, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4440f6dfc6535cd3a1d1bda9eafa92f35cd0273d2d61bafa412c8a989804d70b; original global index 5283.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .triangle 8 0, .triangle 7 0, .gapLower 5 0]

-- Original cycle 4477614c97a43e3517c81ac7dbaf18c721318d4a0086b5a729d315eaa9c5d478; original global index 5297.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 6 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 44c70d6b549216f40c307fce683cba8767a9b775ab30e86c0f5d686f556bba1e; original global index 5330.
def localCycle00062 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -1, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .triangle 12 0, .gapLower 0 1]

-- Original cycle 44efcf38d951f239aa7689e35b0b486983a641a5e9b4f7c8c4164e6e9b210def; original global index 5339.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .gapLower 5 0]

-- Original cycle 452933ed802714826bc0d34e6e5df1b69c7182b56720e0f7527fdf719d4b84ae; original global index 5349.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 45f6bfb9e46b3e114d54d49b752683f8b225c4fc7914693bbfb411ea4cffeddc; original global index 5411.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

-- Original cycle 45fc028eacd876a725098382417da63b239fd517a45e16f6cb48dbfe2eac75f8; original global index 5414.
def localCycle00066 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 4 2, .gapUpper 2 3]

-- Original cycle 460b2f8d3e4b44e7884c70f5c4bf3eb55800e64555836f84c54c90385aa82081; original global index 5420.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 46ba0b4c59f23bfc40bd6883f625a3a1f18da893991d6889c284ddf21e16d242; original global index 5478.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 47f49fb14c1f79eaef5dc3372dc7a62d6221ddc05a2741026bbc5fc5442ee80e; original global index 5570.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![2, 2, 0, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, false, false, true] }
  origin := ![.gapUpper 1 1, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .gapLower 4 3, .gapLower 0 3, .gapLower 0 2, .triangle 1 1]

-- Original cycle 494d88a83faa28d6aefe31377a2c9875cdd7e8536971f79bb6439dfda6b8c0f7; original global index 5678.
def localCycle00070 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 497db7e8ffced3ed2d23a8a264d857ec77ca88a8f328f2b26bae4cc5eea0170f; original global index 5696.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4aac45f5552cc717a02fadca6d794f578a0725e75be2c83f816b1340cd2daf1e; original global index 5790.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4ac9dd33f70434ee4f1c6fb83ca9bb034ae8a0119a4e8e2f931449fa3701abab; original global index 5803.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 3, .gapLower 4 3, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 4c790de86e529a9779bdf159996017e473473385ed67418bd42dfbc3c9fcc2b8; original global index 5936.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 4 0]

-- Original cycle 4c9ea29496a22df8d56cd3cbbe6d75b0e5ae799f30f5751435dcca69ca77b2b3; original global index 5947.
def localCycle00075 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 5 2, .gapUpper 3 3]

-- Original cycle 4d99dae14cd9a5f6c05c2696126d296db5e367aa51e4947803d2723a5d14e3ce; original global index 6025.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 3, .triangle 3 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 4dcacde7906b84587317b52266d20869c8a4b25a55a267fcbd1db0dfef771dba; original global index 6039.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 4ee862cf08a19987a51b2a6e5418af9f35490fb9b6806ae99a6c4ece35c1d27e; original global index 6130.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![4, 0, 0, 0, 0, -3, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 4f345081186b47dfef2ff97df8bf19e656dcb86a7fb6028ab44fcd5b3a6af8f9; original global index 6156.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 2, .gapLower 5 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 505f55887a9ce41e308d0aa9a88027787cee1e9762cbcddeb11ccacabac90c2b; original global index 6238.
def localCycle00080 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 5 3, .gapUpper 4 3]

-- Original cycle 5071265452f357939c18c7e85c8b30b12246227777309db3fc0ab1ef4f793864; original global index 6247.
def localCycle00081 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 51d2de41e01cd24852ad49ef8a3fab79ea780e14eee7f8429fff4c7f98f4e931; original global index 6365.
def localCycle00082 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 52ab42e998b58419a771db11950838937625001f89eedee9e783d55daadf018d; original global index 6424.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 53f8e9012ad56c42841d5af4cd85e68c1d09884bc4cdd4db45513e787d07b372; original global index 6515.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 1, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 56ac74f37e2666606165466eec15decf68712656574a44128a63d503293a6889; original global index 6718.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 0 5, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![4, -1, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 11 0, .triangle 9 2, .gapLower 0 2, .gapLower 5 3, .triangle 26 0, .gapLower 3 0]

-- Original cycle 5786f80aa1d351efa3c2d1bd9893e3c0dd5c06ca10b2a002b85c9145ed6189c0; original global index 6796.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 581a80d99d839b9f66ff25d08e531a60be0668f5fd5819aadb0b6431c8212494; original global index 6836.
def localCycle00087 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 5a6cedec46fc8d36f571e83de18dbfe14fbb9fe591157cd88f989c3e8dd06a75; original global index 7040.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![4, -1, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 8 0, .gapLower 0 4, .triangle 9 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 5b0f69878c3fd2b14d4ac1f8b856ef745a5e2d65a81ea87fe13356db4b65a549; original global index 7085.
def localCycle00089 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .triangle 10 1, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 5cd9a12fafb7b41b41f1cc6e40d01bdf129c393dd04769bbd7b973ba38e6d8cc; original global index 7226.
def localCycle00090 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .triangle 10 2, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 5e61cb079ef0ccf857c0f0af5b7f81f9f2cbdb27fc4b617731286bb9bf001746; original global index 7343.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5ec07883f456e462c93da0f9b065e4dba08e000acdfa37afad88671f9f4a7bd5; original global index 7376.
def localCycle00092 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 622344aea8335b2cd60e4438dbe617bed07463f0eae9796cbeb84c768f5dc709; original global index 7661.
def localCycle00093 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 62518665f674fca4d24a9f8140a28c1162d4ec6eff8c2332b9b9509167319cd9; original global index 7675.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 6727173914c837b04fb9e39b9cae2bcf8543361731ff8b0797f5d8cfe3524012; original global index 8020.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![4, 0, 0, -3, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 691e0b9a4a287fcadfd0dc05d32ea397b3a3bc0bf367a74ed9de958658b0ae3d; original global index 8175.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .triangle 10 2, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 6a9f9c86b2ba1287f12670287cf5fa2572119edeac940393a3ee9db01f6b6760; original global index 8302.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 6c4ba5f5b6d028da1661e1a83092ae82d0ab2651b21a4d3ac2cc4958386855ab; original global index 8437.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![4, -1, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 8 0, .triangle 5 2, .gapLower 0 3, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 6d3b6daeb88c4a2e3905177337b40222b43ea7c0535b9543b6fda3e3ca132a1e; original global index 8496.
def localCycle00099 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 26 2, .gapUpper 2 3]

-- Original cycle 6d50fdb6db3571f45525768e09eb04dc32377e3d998c38c7cfef6a76c7265281; original global index 8498.
def localCycle00100 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .gapLower 0 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 6fa856ad0b233cbaeca5261127e7916fd6fcc631df389aae60f7424dfa5c6683; original global index 8663.
def localCycle00101 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 11 0, .gapLower 0 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 70a4d6ec3dcd58f512f6f71b4e24a6aa9561a5a3edf3e7e0acb1213274089efb; original global index 8727.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 70a96cdd7e6f30f0c3129eaed83734bd30572e70e8c71c34db27c8ebda0b5f8e; original global index 8733.
def localCycle00103 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .triangle 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 70dc4c64dcd8345c12e74689eae12b91dc360652e4ad06243ee8a828625da85d; original global index 8745.
def localCycle00104 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 0 1]

-- Original cycle 712151cf1283c77cf0487e067b9f57d98878cfd3d2330dd3e9f43e7ad7e614fa; original global index 8775.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 1, .gapLower 0 4, .gapLower 4 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 73136d601c5d4abaf9f458444c497f9e2e3d084c25ee8ad7319431dce541707d; original global index 8913.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 74182dbabfd1412417cf6c9f332a9bd04f720397680d85f3d325d6c5d09e1270; original global index 9007.
def localCycle00107 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 744f6916dcd1b1023a1d4ca39998a033ebe0e402543186442ab4cfaf8587f45e; original global index 9021.
def localCycle00108 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .triangle 10 2, .gapLower 0 2, .gapLower 4 2, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 76cba1081143bc84f8d2b6c10f9a2cebc5eabbd8298013a21a837ef2f764e0d5; original global index 9193.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 794dd8d15376ab5110ab4cf9b637d0a23c043dcbf79ba48a4d9e92cc5f8fd457; original global index 9385.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 7bc31bba62ab021d4a70bd59f2040e04c7c15c7da305074232c5c59f090ad478; original global index 9574.
def localCycle00111 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 4, .gapLower 0 3, .gapLower 4 3, .triangle 25 2, .gapUpper 2 3]

-- Original cycle 7df73e0df0351bc9092fa21d71f96ba55b9e4b46840858c70346d367137e1250; original global index 9782.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 80f953ba862b15220765b3dc6d2f50d4e0b1dde8462d2010d1cbb918c6699d6b; original global index 10009.
def localCycle00113 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .triangle 10 0, .gapLower 0 1]

-- Original cycle 8147cec10cc223b217b34766337bb4b01dd15435bdd06c531a59729c740753c0; original global index 10038.
def localCycle00114 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 1]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .gapLower 5 3, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 8304937ab41114646e4d92e2e409f3095d3c8a3d5a4c53f9444ab8233406afa1; original global index 10160.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 3, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 848d0fdd3fee6f32a020967b12792cbc541d523a8f5cbc8d1d27b0671401e222; original global index 10294.
def localCycle00116 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 85ca3457dd7a5a102f5fcb90b6ce79a4826df73fda2f6eeb4111423698826745; original global index 10384.
def localCycle00117 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 2, .gapLower 5 3, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8604cf705b5f34a506fe383518c4414a160d1fe5427b48382bfd59266d48a708; original global index 10396.
def localCycle00118 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 87208866c040373081549485a40bcea3a18eb787379896bd633681302ba81c2f; original global index 10484.
def localCycle00119 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 6 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 87ad0bfc52a24cbd4e8dda51f1bc63f3e8b276cad75b30022bf88ea688346026; original global index 10518.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 88f5bda2af62b0df380fc434903a9ca6c4618a3e84054cb0b82fbeaf4ec18485; original global index 10606.
def localCycle00121 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .triangle 9 2, .gapLower 0 2, .gapLower 5 3, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8a579c2df132e1b17eff3c8e1bb1dd90197f76f5138b7638aefb7a80e7ac2267; original global index 10720.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8a5af7e1ffe6120f33c6b599d1c7636a63f2ea39ac0a8696679f98b81da16b0e; original global index 10721.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 2, .triangle 18 1, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 8a71c10ece43710c3386398052b580cf009cf29ab2010169d3e89739285cb20b; original global index 10727.
def localCycle00124 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .gapLower 0 3, .gapLower 5 2, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8ae9654e825f51c433ed66fbf1c2b0ee3abd1fa08290b624afb90c8dbced2531; original global index 10765.
def localCycle00125 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle 8b8ae8c13e72a2c91cf8f870572637db08486b2e5f18ab677b7e0b03dc0244bd; original global index 10809.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8bb876ec730ddb29aaac7b1211d51d9134d62d1e676cd63837cdfd4a07ddc093; original global index 10816.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .triangle 9 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8e16c6a100efbc6f070f54e2bb0e214d69cdb3a0ff2b9558fe3f2ecdeb6a9049; original global index 11003.
def localCycle00128 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 3 3, .gapUpper 2 3]

-- Original cycle 8ead36a71a8a99af5943501e9ba54b0d2be55f7f2d0b248bde619ac49d9b75db; original global index 11040.
def localCycle00129 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 8ebad7ab44573f06b83e943ebbae836831800dc62bb2ea6a7688d04f2b113815; original global index 11044.
def localCycle00130 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 5 1, .corridorLower 2 3]

-- Original cycle 8f67f13a922b35c73352bc0e3ad0aa855867f7cf0e47c392e7cadec67a06278d; original global index 11096.
def localCycle00131 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 5]

-- Original cycle 8fd0a2e42e7471dfa81a36feea10275d145e411dace8e6cb25173494c5c8eedd; original global index 11131.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 903d605ab01270439155845fed5a9b3d29ef72d51579982eac87da37e6fe41e5; original global index 11166.
def localCycle00133 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .gapLower 4 3, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 924a79874e9df2bbbb2ab03d2dfa84217e692349de4ed1dec789894a0c93f9b4; original global index 11331.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 927ea5625420449bf80abd6f15cf6c8f520f9b76eb2d1950c7bbe22d239791fc; original global index 11347.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 932df9426d47fa605f334f32cdb44fa5241b8b9c48c845ca88ed580cfbbf7023; original global index 11414.
def localCycle00136 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 7 2, .gapLower 0 3, .gapLower 3 2, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 935c72865258dca2a93569ed2965ff2c3f6f3fc62b58baa71b2de0b52c0e7395; original global index 11428.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 943931e552a11e0f37f5a063c1c1431870ecbaa5838e478524553842457ef78b; original global index 11499.
def localCycle00138 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 3 3, .gapLower 5 1, .gapUpper 2 3]

-- Original cycle 950ad450a51cdbda6a2d49f103b93a779e370c451a71e4b6c63487387fab93ec; original global index 11574.
def localCycle00139 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 96ab70f24a5cf79c633a5a6ead5763726717e8039bd9860bfab8b688b2d26c9d; original global index 11713.
def localCycle00140 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -3, 0]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.thetaUpper 1, .gapUpper 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 974f1ebeda31fc5d80bf5b1c9a84b2c6e1b70962e2a16f8f1cf9e97dd1000237; original global index 11758.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 9abb7c78775ff52fcbf21bb1d18f15040fdeb0e4b13f7db2af5fa07debc95cec; original global index 12025.
def localCycle00142 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .triangle 12 0, .gapLower 0 1]

-- Original cycle 9bf69a907e29d8c21f35df633a2db818650d4416b5a74ca3bd05e3c02706d29a; original global index 12129.
def localCycle00143 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 9c4f9d97e36e58b3cadf250e77cc64fa7c7c5d0810e1241e87e7be3a6907d63e; original global index 12160.
def localCycle00144 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 5 1, .gapUpper 2 3]

-- Original cycle 9d166dccda2fca80cf6fb7e523eaae64bf78343abaa40c79d32bbd09c886e291; original global index 12217.
def localCycle00145 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9db178a8727606012abe887da5f119299eab11ea8eba866577b52422f119ddd3; original global index 12268.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 28 2, .triangle 26 1, .corridorLower 2 3]

-- Original cycle 9f7197df8cf397bd9302894cb0b0fe21fb36b3cae82b83f4e939a89fab46c366; original global index 12409.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a0c911a24a365edfba01b995767e55ae72e8dbb87d6f6d2001d1636e5201b9aa; original global index 12509.
def localCycle00148 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .gapLower 4 3, .gapLower 0 3, .triangle 10 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a164dbe476cb29841c77be74f5dc76366f37b97a7eb985e0e79dd2fb30c98d94; original global index 12550.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 2, .triangle 3 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a1f784916a81a9f04fac278120bd260890772f8a245b00bd3253f12bbc1a216d; original global index 12595.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a28d49a5d018b07944f02cc358aba1c442fccdf06c01bca05f0e668aeeb3f5cf; original global index 12644.
def localCycle00151 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a3482ade968ac1be7937a7211345573293bfeecd485b35d4682456e56e362138; original global index 12688.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle a5eef2074a149b70a2dd2f9331240f41c9959744ab8187b3fb0c931b588e2187; original global index 12894.
def localCycle00153 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle a88f0f24833edb0548995a00be08745e6b0e661a7001c6625fca4f24a2554779; original global index 13117.
def localCycle00154 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle a8bc5caf207271dd1eecf0c94cea09dc33263836430816187a3ab849279f42fb; original global index 13134.
def localCycle00155 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a8de46fee15b16db1a30b54bba1887a1d38958f4e9f68cba96b474ae78332c91; original global index 13146.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ab0c062d4f116434b06840424c3439734ec819311503d219a08c2658a62c839c; original global index 13323.
def localCycle00157 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle aca169d432fec6477c82f29e4596f7f397c22cc5032eb8a4e66029250235ab97; original global index 13458.
def localCycle00158 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle ad1b002a8103331fb22d175a7310553635afbc7db3bed112daf6fd0890325d51; original global index 13494.
def localCycle00159 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle ae733903d8601094c91de934965094c52e3cb75430a457c060b3a089dbcbc5fa; original global index 13616.
def localCycle00160 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle af5dab388193bcf9046865a90c4b33f716f06a936e78fa60f2556a4b6dbad391; original global index 13698.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 10 0, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle af80b9228b17629cab283e0a4c1c8195569772000a2034e95203dd226ffd6e52; original global index 13705.
def localCycle00162 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle afe1f1ab78b04c74a8971ace8e699178b84e71b5aef63a436ce2dcb8c10e7d6e; original global index 13737.
def localCycle00163 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b008157ff5248b72bc684d2e740e08a8235c90b80c253ff58d295d58c592946b; original global index 13742.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 0, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, -2, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 0, .gapLower 0 6, .gapLower 0 5, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle b0f9271c6f5df99038f30b2a52b0e1c50c3c9c6c7aa8a6e0529c3dcff30ea809; original global index 13815.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle b1112f8aa688f61368ac936a0ac87925044bebaf9a6f74dd40aa8924fb8ab14d; original global index 13824.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 14 0, .gapLower 0 2, .gapLower 4 2, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b11d12b03fd6ecdbc5d0a6d6e5707210287154f72e7c928ff5c2f8bf3a145a6b; original global index 13831.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle b137b1af89676cbd736e1bc61ae9deeef481e2861e5fe2029c3b4aa8c87bd137; original global index 13842.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b2509832cc3c23f5e6afcca0739d046083d720cd9efeffe72bf2d9a3b3305556; original global index 13935.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle b2cf0c508069cfbd5f67341c94ef77f9c3f37fe2ceedb4b425a827df485a5f6b; original global index 13978.
def localCycle00170 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 1, .gapLower 0 4, .gapLower 5 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle b53e941321b72b65a71a06fdcc3de648b4c4b76570fb9162937e4e21ca028f3d; original global index 14161.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b547f9eee5662146c634ccebd2dfa5936c3abd27e761094684f9a93d432a5c61; original global index 14163.
def localCycle00172 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .gapLower 0 1]

-- Original cycle b640fed98b0eca5d95cf7f3024eda0e963a236a90df9ba868fdbc266920d5bd2; original global index 14240.
def localCycle00173 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 2 6, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 8 0, .triangle 7 2, .gapLower 0 3, .gapLower 3 2, .corridorLower 2 3]

-- Original cycle b70605d6737ef11b614141fb2554cc9e002190c1a576d519a5c5fc861a6b9fed; original global index 14296.
def localCycle00174 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b76ebf9fb0d46428e98504b422b471dd870c8255d6fc0e9f1c582c08d92f5b0b; original global index 14317.
def localCycle00175 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 0 1]

-- Original cycle b9599d7f50404a61f2b5a10d64d4e52496cb1da25e710acf482439bc47d82e6f; original global index 14462.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 14 0, .gapLower 0 3, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle c081735dfdfeab0b506ddfc985470aebef06270f1525cbb83d3857c04a8428b4; original global index 15028.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c0ee9708108ee37d674968f0c1efc141b512e22c3788d41876f8f8db40fd1370; original global index 15064.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 3, .triangle 25 0, .corridorLower 2 3]

-- Original cycle c4eaf29bffd84e5e63fd5d42bf4079bc165f44fbb9e0112dfb9b9360721d9870; original global index 15365.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, 0, 0, -3, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle c5e4f74a8006afc2966e31129ddf396b9d48c18cf8937a50b3779d0aa1cc941f; original global index 15431.
def localCycle00180 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle c94dd3d37e3fc33a9acb62f638f548e91dde3417d1d02e43b6269319effe9636; original global index 15737.
def localCycle00181 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle ca9b4e5720bc3405cc44b3e363dd511a652e5ef808b46f85d8a4e2393e013d13; original global index 15841.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle cec9c8e46aaded734ddca5cc103fdab0d0e0a2fd15cde6ae098ccfa614e80a1e; original global index 16143.
def localCycle00183 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 7 2, .triangle 10 1, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle cf002dfe8e042812317346e2b8f8b27f05cfa698e3059dc15972c6f69f56d921; original global index 16153.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 1, .triangle 6 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle cf36fa1285d1e5b25b8f38e17013fdb81e635123a3805d648a808e2abae8f67c; original global index 16173.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cfab7023a043e2cab774440b7982f47de66f5b6fe60feee69c564047205a6348; original global index 16207.
def localCycle00186 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 5 2, .gapLower 0 3, .gapLower 5 2, .triangle 26 2, .gapUpper 2 3]

-- Original cycle cfef05b5da2fb321b564667fcb3de153b4a75d455dbc2155815e90768742f02f; original global index 16227.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

-- Original cycle d10ef0e61d9d877f069049a87c19e41a14ed209e9f28872d5a3dc4e248fce0ad; original global index 16325.
def localCycle00188 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .gapLower 0 3, .gapLower 3 2, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle d3b5cbac57da83662f63690d5f59b3a11636a8228d47ed87ff19cefc05b458eb; original global index 16521.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle d3f0ab1cc517680327776045ea4b90fc8785d2bf73813029bd9d4b5ae8cfb6ca; original global index 16542.
def localCycle00190 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 5 3, .gapLower 0 2]

-- Original cycle d41a603be07aa6585508ae37336079213e15f89d3a0daed738c9862ded46616a; original global index 16552.
def localCycle00191 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle d4c8ea0f1d9c8d28578216c577fcaabced972a6ef0a9214463db92b35e7e48f1; original global index 16601.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle d59e3b7a9c83532d4b98bc9c1ac58124d48c802072f6d009918271363ed9e448; original global index 16674.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle d7ce4278f55fd4358966dd8e194fde524cfca995afbf81da5da36c4b15361b34; original global index 16839.
def localCycle00194 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .gapLower 5 3, .gapLower 0 2, .gapLower 0 1]

-- Original cycle d9005f2e4df6f76c617857ffb18819d509894101d102d7a63909e784da5e2071; original global index 16947.
def localCycle00195 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle d971d7de2cded3412e343190e6251c9af6307235e1fb97b17e4b7b7887536e49; original global index 16994.
def localCycle00196 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 20 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle dbf915d41c26af1817670e3fcd289f713a3ccd5a39409d28d2f96f457c421f34; original global index 17194.
def localCycle00197 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle dc10a19fdbd3649fcd27375ebac33664bdad554f68c4fc0a1f75a832c81c3bd0; original global index 17200.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle dc2d88011d27248fe1a78439f37415b840eb4425a01634c48b313669bfb23745; original global index 17207.
def localCycle00199 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .gapLower 0 1]

-- Original cycle dc5044ac7d7e44e183cd058bf2b554110e1df4910b6ff16de88cc2cc91fc8bb8; original global index 17217.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![4, -1, -2, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 8 0, .gapLower 0 4, .gapLower 0 3, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle dccc82d32b76f4cab5d9dacbcc447555166647b935084c52c94a56cab644892f; original global index 17253.
def localCycle00201 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle dce4d8e852fdb48f644b32773505668e7c4583579dc26ab9525b81537c3ab7df; original global index 17265.
def localCycle00202 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle dd0c9b63a447098b2b737551bb1c3470c16e0a8dccfdad8d7bbea21419728c70; original global index 17280.
def localCycle00203 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 0 5, .distance 0 3]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 5 3, .gapLower 0 2]

-- Original cycle dd364190e3f861743a655ae220ed1cdb0f4f10dd510a8bb0bdffe0e745e3b74a; original global index 17297.
def localCycle00204 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .triangle 10 1, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle dd393610939a3529612a5e288de36f3c1501497586bb73353e6ccc91fbe8c8de; original global index 17298.
def localCycle00205 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 3, .gapUpper 3 3]

-- Original cycle dd72740fc451e487445d50b903d41790c74bb3091f1c5c5a78c22a37f0948bb6; original global index 17312.
def localCycle00206 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ddacdc9f01a339f40bd2f3ff214f91d7c18a925be1f9c86255fc4089647e5db7; original global index 17329.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, 0, 0, 0, -3, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4]

-- Original cycle ddfe0452c1acc4785db8da80dfa4390c28c70c3d03a411638577fe23797f1b9a; original global index 17356.
def localCycle00208 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e01089b7a7abcaaf85830e2193b6b1f0fa40a683069685ad2b992300779a7bca; original global index 17517.
def localCycle00209 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 3, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle e0c69ebb151603ea799459b7a0d52a0018170e3a17e8c54fda592dd930b2b66d; original global index 17575.
def localCycle00210 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle e178a9f5c514a83f0a155b70032659774357131faf92de62e84cd5530caaeab1; original global index 17631.
def localCycle00211 : Cycle where
  length := 17
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -1, -1, 0, -1, 0, 0, 2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapUpper 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle e2d2149441836e3ea635ddd31a3d7dd28789f8c5a0a71f38319efaafe2bde239; original global index 17739.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle e80afdae1a03a6f16aaee9bb1b9929ff4edf80e553585dff660111356c843ed9; original global index 18145.
def localCycle00213 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle e880904e838327eef86313a55a7b4a5e7b5b147d6da1cee9630352d7523b16e8; original global index 18173.
def localCycle00214 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 5 1, .gapUpper 2 3]

-- Original cycle ea46edf6fbfaed9e69db3b4158211ce827a9b96955d4dca524cbb68b73c1dbab; original global index 18295.
def localCycle00215 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle ec1df3dc060ad86b96b9e61e31185df3562a826c9c28402b166e3235c56aa03c; original global index 18434.
def localCycle00216 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle ece53d96cbc941bde86cd1b54d503bb8d09dad1901d050038a841f84c1aec5ca; original global index 18492.
def localCycle00217 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle ee639fe3505fb79702cb229643469bc40b62e73c8ce217192615c30f1d745f72; original global index 18609.
def localCycle00218 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle eebdb3f16bb2c4fb32a9496c430e5eb66c563a413105bb3ecc473578af58d1f2; original global index 18633.
def localCycle00219 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

-- Original cycle f037ef4f5b3e292f61ef726ab3a109228903235e8a322db0670b39e6ee6edb30; original global index 18736.
def localCycle00220 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f1b91b650ce34ee954a88f05ba53770a75be65d202f1e59579c0c36f4ae9f965; original global index 18849.
def localCycle00221 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f227f16a675e5885b7143bb413f6f54ba1acb776f52a2c1df08ad2c075ec84e9; original global index 18885.
def localCycle00222 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .triangle 7 2, .gapLower 0 3, .gapLower 3 2, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f250c6afcf52e551a527cfff5b369c8165585f5ab866cfc64a3b870b881e530a; original global index 18899.
def localCycle00223 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 4, .triangle 10 0, .triangle 26 2, .gapUpper 2 3]

-- Original cycle f3378afa01305b33f7efacf444f2f238cbf0ca8bac18943db6eb8d1ec5ffa9f9; original global index 18968.
def localCycle00224 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![2, 2, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, true, false, false] }
  origin := ![.gapUpper 1 1, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle f3829b7f72b2380ca3c0cf9713c573eb64c9337cbe7715f67e825039c066cee5; original global index 18997.
def localCycle00225 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle f5cb0d8f1edb652ccff7498deb0c8124cc1ec8f6365dbb9acaf38dcaa10d8bad; original global index 19176.
def localCycle00226 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle f8971e88772037acf945be370e2f7afca5c31e606cafc10022b30f3720a17e60; original global index 19387.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 10 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f9248779f9eee9a0cf6c7003d46f65c3efd9b2240f0143a8841e12beef7eb3ef; original global index 19430.
def localCycle00228 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![4, 0, 0, 0, -3, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle fd395717e29f08e5bb5e8c5bacb150c52cdbf3ed6be994c7fda3643935ac7106; original global index 19789.
def localCycle00229 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 3]
    constant := ![4, -1, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 11 0, .triangle 10 2, .gapLower 0 2, .gapLower 4 2, .triangle 25 0, .gapLower 3 0]

-- Original cycle ff1233e8cd28d6ae3ddb0e2c9dc46f5b2e09a848f0021d0cfab115a710d082b8; original global index 19939.
def localCycle00230 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaLower 1]

-- Original cycle ff1fb9b8abcbc2f0b090e2b3d0cdf18f37725074f2203587fbbe624b1ebbae97; original global index 19946.
def localCycle00231 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

def library : Library := fun id => if id < 116 then (if id < 58 then (if id < 29 then (if id < 14 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 10 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))) else (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))))) else (if id < 21 then (if id < 17 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none))) else (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))) else (if id < 25 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)))))) else (if id < 43 then (if id < 36 then (if id < 32 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))))) else (if id < 50 then (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))) else (if id < 54 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))))))) else (if id < 87 then (if id < 72 then (if id < 65 then (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))) else (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))))) else (if id < 79 then (if id < 75 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 83 then (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))))) else (if id < 101 then (if id < 94 then (if id < 90 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))) else (if id < 108 then (if id < 104 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)))) else (if id < 112 then (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))) else (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)))))))) else (if id < 174 then (if id < 145 then (if id < 130 then (if id < 123 then (if id < 119 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))) else (if id < 126 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))))) else (if id < 137 then (if id < 133 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 141 then (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))) else (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))))) else (if id < 159 then (if id < 152 then (if id < 148 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))) else (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)))) else (if id < 155 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))) else (if id < 157 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))))) else (if id < 166 then (if id < 162 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)))) else (if id < 170 then (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 172 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none))))))) else (if id < 203 then (if id < 188 then (if id < 181 then (if id < 177 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))) else (if id < 184 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none))) else (if id < 186 then (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none)) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none))))) else (if id < 195 then (if id < 191 then (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))) else (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)))) else (if id < 199 then (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)))))) else (if id < 217 then (if id < 210 then (if id < 206 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)))) else (if id < 213 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))) else (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none))))) else (if id < 224 then (if id < 220 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none))) else (if id < 222 then (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)))) else (if id < 228 then (if id < 226 then (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none))) else (if id < 230 then (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 5, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 155 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5760)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 0, 5, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 2, 0, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![140, 22, 190, 133, 66, 78, 184, 113, 117, 148, 127, 86, 86, 114, 113, 113, 113, 113, 69, 203, 203, 79, 30, 6, 45, 29, 105, 61]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5761)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 0, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5762)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 0, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5763)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 4, 3, 2, 6], ![5, 3, 4, 0, 1, 6], ![5, 2, 0, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 42 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5764)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 109 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5765)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 28 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5766)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 39 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5767)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 139 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5768)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 221 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5769)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 218 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5770)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![226, 175, 229, 75, 138, 49, 165, 104, 57, 76, 223, 157, 64, 201, 186, 104, 104, 104, 145, 223, 108, 166, 99, 124, 25, 20, 223, 53]) }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5771)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 195 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5772)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 72 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5773)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 5, 0, 1, 6], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 156 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5774)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 4, 0, 1, 6], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5775)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 4, 0, 1, 6], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![140, 172, 85, 205, 1, 179, 77, 199, 149, 115, 3, 125, 5, 224, 199, 199, 199, 199, 44, 3, 121, 59, 111, 32, 73, 153, 3, 216]) }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5776)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![5, 3, 4, 0, 1, 6], ![5, 2, 4, 0, 1, 6], ![5, 2, 3, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 180 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5777)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![226, 175, 154, 173, 214, 207, 7, 104, 161, 176, 36, 93, 43, 227, 104, 104, 104, 104, 23, 204, 183, 11, 188, 136, 222, 89, 170, 164]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5778)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 116 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5779)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 191 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5780)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 94 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5781)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 158 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5782)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 5, 4, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 17 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5783)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 26 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5784)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 151 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5785)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 17 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5786)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 181 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5787)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![226, 175, 4, 9, 128, 228, 84, 104, 57, 76, 126, 217, 64, 201, 104, 104, 104, 104, 103, 96, 90, 55, 209, 81, 12, 13, 144, 19]) }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5788)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 2 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5789)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![140, 62, 51, 9, 128, 228, 84, 142, 21, 76, 126, 211, 192, 194, 142, 142, 142, 142, 103, 46, 46, 8, 209, 81, 12, 13, 144, 19]) }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5790)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![140, 172, 80, 16, 128, 95, 31, 199, 149, 98, 144, 230, 193, 224, 199, 199, 199, 199, 44, 35, 27, 24, 200, 100, 101, 231, 88, 135]) }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5791)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![5, 4, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 208 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5792)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 2, 6], ![5, 4, 3, 0, 1, 6], ![5, 4, 2, 0, 1, 6], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 213 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5793)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 163 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5794)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 122 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5795)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 47 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5796)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 0, 1, 6, 3, 4], ![0, 2, 1, 5, 4, 3]], proof := .tail 150 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5797)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 3, 6], ![2, 0, 1, 4, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 197 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5798)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 3], ![2, 0, 1, 4, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 47 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5799)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 5, 6, 3], ![2, 0, 1, 4, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 147 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5800)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 0, 1, 6, 4, 3], ![0, 2, 1, 5, 4, 3]], proof := .tail 168 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5801)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 132 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5802)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 1, 4, 3]], proof := .tail 177 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5803)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 0, 6, 1, 4, 3], ![0, 2, 5, 1, 4, 3]], proof := .tail 65 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5804)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 4, 1, 3]], proof := .tail 220 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5805)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 0, 6, 1, 4, 3], ![0, 2, 5, 4, 1, 3]], proof := .tail 54 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5806)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 4, 6], ![2, 0, 5, 1, 3, 6], ![2, 0, 4, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 47 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5807)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 171 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5808)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 174 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5809)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 182 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5810)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 182 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5811)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 210 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5812)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 1, 3], ![0, 2, 5, 4, 1, 3]], proof := .tail 52 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5813)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 63 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5814)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 0, 6, 1, 4, 3], ![0, 2, 5, 4, 3, 1]], proof := .tail 54 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5815)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 1, 3], ![0, 2, 4, 5, 3, 1]], proof := .tail 87 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5816)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 1, 3], ![0, 2, 5, 4, 3, 1]], proof := .tail 0 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5817)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 3, 6], ![2, 0, 4, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 33 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5818)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 3, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 119 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5819)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 3, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 3, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 182 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5820)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 6, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 83 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5821)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 162 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5822)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 118 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5823)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 3, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 219 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5824)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 206 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5825)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 67 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5826)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 196 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5827)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 132 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5828)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 6, 3, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 58 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5829)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 141 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5830)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 60 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5831)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 47 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5832)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 129 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5833)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 185 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5834)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 1, 6], ![2, 0, 5, 3, 1, 6], ![2, 0, 4, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 56 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5835)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 212 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5836)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 212 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5837)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 6, 5], ![2, 0, 3, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 178 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5838)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 1, 6, 5], ![2, 0, 6, 3, 1, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 68 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5839)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 6, 1, 5], ![2, 0, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 141 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5840)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 1, 5], ![2, 0, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 106 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5841)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 1, 5], ![2, 0, 6, 3, 1, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 159 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5842)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 185 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5843)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 1, 6], ![2, 0, 4, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 189 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5844)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 6, 1], ![2, 0, 3, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 91 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5845)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 6, 1], ![2, 0, 4, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 34 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5846)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 3, 1], ![2, 0, 4, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 134 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5847)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 6, 1], ![2, 0, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 130 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5848)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 6, 5, 1], ![2, 0, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 97 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5849)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 5, 1], ![2, 0, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 215 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5850)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 5, 1], ![2, 0, 6, 3, 4, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 37 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5851)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 6, 1], ![2, 0, 4, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 18 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5852)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 3, 1], ![2, 0, 4, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 134 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5853)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 5, 6, 3, 1], ![2, 0, 4, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 48 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5854)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 3, 1], ![2, 0, 6, 4, 3, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 131 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5855)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 152 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5856)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 14 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5857)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 107 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5858)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 120 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5859)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 120 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5860)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 110 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5861)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 1, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 1, 3], ![0, 2, 4, 5, 3, 1]], proof := .tail 10 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5862)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 71 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5863)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 3, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 167 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5864)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 6, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 3, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 137 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5865)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 6, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 74 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5866)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 187 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5867)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 1, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 38 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5868)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 155 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5869)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 5, 0, 3, 1, 6], ![2, 4, 0, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 202 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5870)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 0, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 225 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5871)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 0, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 102 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5872)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 0, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 112 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5873)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 5, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 0, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 102 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5874)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 0, 6, 5, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 0, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 15 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5875)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 5, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 146 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5876)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 143 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5877)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 123 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5878)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 5, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 82 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5879)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 160 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5880)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 6, 5, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 198 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5881)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 3, 5, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 6, 1, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 1, 3], ![0, 2, 4, 5, 3, 1]], proof := .tail 169 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5882)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 5, 1, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 50 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5883)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 3, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 70 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5884)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 6, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 5, 1, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 3, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 82 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5885)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 6, 3, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 169 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5886)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 6, 5, 3, 4, 2], ![3, 5, 4, 0, 6, 1], ![2, 0, 5, 6, 1, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 40 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5887)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (5760 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 5760 ≤ id.val) (hhigh : id.val < 5888) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 5760)) = true := by
  let j : Fin 128 := ⟨id.val - 5760, by omega⟩
  have hsum : 5760 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (5760 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard045
