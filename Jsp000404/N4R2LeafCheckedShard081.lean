import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard081
open N4R2RowDataReplay

-- Original cycle 002efe5cb9457474714fd19592e63b6386484b1d201f70654b507ac0e48d147c; original global index 18.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 01c1e79fe663d65cc9206598e53e2000a9950ab5fa8a2f81c4800d5d20f7b0c1; original global index 141.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 01c68689ce0fba83f8224e43f34541d0cc533a35a2a9c0b5528422478e2484a9; original global index 142.
def localCycle00002 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 045177addd8632b6124533fe8877185d39e178582f6b5af61a0fece59458aad1; original global index 341.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0451dbd8f382534b6827c272d2fc88f718354ea99e7ce11223f4207ff7a46867; original global index 342.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 0693bcf8682f89d0eb12b2922198695ec0c0be087d0472c2e5579ea0cbfc741d; original global index 542.
def localCycle00005 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 083a27174afa4bf24d2b2c536bf3dbe634989607cfe0e4a681e11f6e6d3b6cf4; original global index 657.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 09c2fbd2a4b98525759086c5002994ac73e48a5e3c20773218599b37afa544bb; original global index 781.
def localCycle00007 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00008 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0b81a868916d0d5a43f74695731a21b06ef891279018029e53b704b6ab2f4197; original global index 924.
def localCycle00009 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 18 2, .triangle 23 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0e6b556ce32f68363cb6410896149f3ca1112cf82a834c7163240593e0c4ef24; original global index 1141.
def localCycle00010 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 17 1, .triangle 7 0, .triangle 0 1, .triangle 1 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle 0ec4e83fd5ce31c7b25da4a69acf0cf5659e146e33aba5733d871def85e6e1d1; original global index 1168.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0f7c1a710e16d310a641c1df2c1a73c9312df8d439c8e192df585db9ba1cc157; original global index 1229.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 6 3, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 1143ecf51ec381dd114ffd41188c6a260f8392a1f38d0b334099ba9d6cde4633; original global index 1371.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 136ab72e26dbd2080bbd3bd88c41798d78f1136d9362f19a6ffa28537b850973; original global index 1529.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 2, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Original cycle 156b777143e47af89725913aaccc1759e20ee561de4259c78bbed3f3d93f30cb; original global index 1696.
def localCycle00015 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle 17de58b227b6ef75acd1508f41eb971b3081e7b315dff25a5f2eeceedd16987e; original global index 1866.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 4 0, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 1bae60ba5962d4746e6424fc8c0e5e5af2a4dc05474315f55e476cd0cd600722; original global index 2142.
def localCycle00017 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 4 0]

-- Original cycle 1c9165379786262bf9261a85e346d3d8929a48ea7e5b62b177279715c2993cf2; original global index 2199.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 2, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .triangle 8 0, .triangle 6 2, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Original cycle 1d9672098015bcb53d08fcde07495b16767884f0bf11ba9744b1539f06d8d186; original global index 2275.
def localCycle00019 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1e065326c60e2c02814b5a3b2005125e91164232d16923f2008c69f5b6e8986e; original global index 2308.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 22544f970e4bf7c5320568e23b852a1cc1258bd9d511a87075ba12f18d1b4277; original global index 2630.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .gapLower 3 0]

-- Original cycle 240e859059e15910566bf4fcd50fc3057037ae142e0ed50d9214a3584c163f0c; original global index 2761.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .gapLower 2 0]

-- Original cycle 26218ba9199cca86ca88d1bb96a47cffc0067fc22fea199d466458ec7c15e4b9; original global index 2921.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 27830c1e46c0f5394ca5d7c7afce63e589c08b0d22802724b04b2f805ffd1350; original global index 3024.
def localCycle00024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 30 2, .triangle 18 0, .triangle 16 0, .triangle 6 0]

-- Original cycle 2958fb68c875ad3854699bdb4e1a014a9915ca8a8d6a576cf8d831eedce3f2b6; original global index 3155.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 2bc31b3f9c5e5ca20a7b531f635d916511731e9bf0b7eac2ea52fea9bb6c8b4c; original global index 3344.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2d080be512d8d23db6205a7cb89eb007ab01be83b366d58b74d77ac44af54038; original global index 3439.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 2dd233b0e6a672884cf178d9ae13273ed0b1d3b8c8173d88390000e0819d48db; original global index 3498.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 2e25a51613dcd9c39401b807d14bea5793952aedd03fbb7212199a51abdd1756; original global index 3525.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 2ee5791340d960176180a512dbf286ff4736ef56845f359745bedc8a111c7535; original global index 3586.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 2eed69d6991fddb8c9e6d829183aea191d1b3a55a901e07d91eecf3df201e5bd; original global index 3591.
def localCycle00031 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 30089ac32af57a37757cdec1a1ea92dea8cd7f8276cd9c7293187023edeee791; original global index 3661.
def localCycle00032 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .gapLower 6 2, .gapUpper 2 3]

-- Original cycle 318e9357ac06b320f384bda43d31d59ba7bec5cfa9e29b4a7787c29b5a9d1ef1; original global index 3781.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 31a21680932c85504034cd0457ef83845205744e247dc8260bcaeb47d2b5392c; original global index 3792.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 36bc0c571b4d838f4b243a740521fcee25f09c050ce1c8e979b502a623ceabeb; original global index 4207.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 38b13d1283774bff6d0ccd80ef31b454411c52084ba0f2e891f2c5cf7c67e472; original global index 4363.
def localCycle00036 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .triangle 29 2, .gapUpper 2 3]

-- Original cycle 38c8321448c76a7cb758c7eb14697f19cf6a286fae5ff2cf60ffc955204bd611; original global index 4369.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 38f97fbf110bc64e896e2ec450d2d76af66314a0554a0604c1e0cdabd3054acc; original global index 4384.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 3bbf7cae30220df3299784b8e1951737c549f60fe43093552aa582eb7180cfbe; original global index 4620.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .gapLower 4 0]

-- Original cycle 411a857e3d1c200a9b44b7dd475550e8159044b1a5743c58baaed9a60256cab4; original global index 5024.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 17 1, .corridorLower 2 5]

-- Original cycle 419400de21ae7c62b0d2f8f33935d96abfb4077a915a9903f181ade6d6c7696d; original global index 5058.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .corridorLower 2 5]

-- Original cycle 4266614f088427d2b310ee8dd047b93443adb68d18d6e0a7e145e2accabdea64; original global index 5115.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 4301392bd3e0c031dffb66aa898972846929d0b45a0294c86777015e80ef2227; original global index 5169.
def localCycle00043 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 454c558b369f8feddb56642ff317cf2705e5e244621d125652bc247dfac08807; original global index 5361.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 45f1a5552ac69a7df9a06ea30cb92391f0dba700f0b5988b8747d054e6d56acf; original global index 5410.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 466dfa4136e8192464a0ecedcba96f2eba02b5211613191e760ed4b4d568581f; original global index 5447.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 46c6348d0d3e3126903c0c643ff09099e05ec4dba249293e88998cde028e3b44; original global index 5483.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 46c9b5bd77ed4582fb0ab46446e47fc1a04dd308115089a85aff0a7506188606; original global index 5484.
def localCycle00048 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 1 2, .gapLower 6 4, .triangle 4 1]

-- Original cycle 485164a8804c88950152011fff6618e2da2d075c1f8155887bf963616aa71f66; original global index 5599.
def localCycle00049 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![-1, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 13 0, .gapLower 6 2, .triangle 30 1, .gapUpper 5 1, .triangle 12 1]

-- Original cycle 4855d3ed76937e44284c839575342166b45745b3c901822f86ac1ae329417785; original global index 5600.
def localCycle00050 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -3, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 4 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4c0e3089b94e4d63dcdf359f85c360ccf3d84cef123d6916753edec13ef5759c; original global index 5905.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4e8f17e128ebbd0449cbd469df54185961929bbd9eda8588dfcdf1f05628d793; original global index 6103.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 4e9451ba2af53c94b76ff4d0e792779f0bab314233cc39004ec4a7f49cc46c74; original global index 6105.
def localCycle00053 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 2, .gapUpper 2 3]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00054 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 52895d20c08e07148768414247d8969445d8fb8ede8b642c656f82e909695eb1; original global index 6417.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .theta 2]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 17 0, .triangle 18 2, .gapLower 6 4, .triangle 13 1, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00056 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 52be2fc56af4af001de59daa8110f62b6f0102a62111a281e04c60c0c436ed9e; original global index 6435.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 53c3af1be176416e247aa6fb979fe663f9b15977875c9019e0e1d96202639b33; original global index 6505.
def localCycle00058 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 551820fec0512b72d295ef6572f15610dce502a3820360008e0e2c8e09d9b57c; original global index 6590.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .gapLower 4 5, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .gapLower 4 0]

-- Original cycle 57648e00f2578f6edf714af76a209449706100538db76bca1ee302a4cca25146; original global index 6776.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 57bdf84e5a919c986d7f241ecfd7169e39cb47dddcbdd7c99de261a12f962915; original global index 6811.
def localCycle00061 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 57e5b8f45e6843881ac1f3aef34750bcc49e32fb47be8189062ec09bb4b5cfe9; original global index 6822.
def localCycle00062 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 587c0dd52868c3ffb6ac5d4db382157ef104ad36c5e0841959888ff1587c5ac7; original global index 6865.
def localCycle00063 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 2, .triangle 17 0, .triangle 0 0, .triangle 1 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle 58f356f88dd47605c066f3a2c5332c9ad35da2cf2396f57148f0b00ff46b238a; original global index 6898.
def localCycle00064 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .triangle 24 1, .gapLower 6 1, .triangle 4 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5acda26beb4a101904bdb5f433bfe3076301c7db29dcdd1a47a5fd0abaadabdf; original global index 7071.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 5c5ab819e37fcc26db3ee27d1f37d61be95c203ea48570617c813a8ddb77e5b0; original global index 7192.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle 5e9d348df1212f9d94801397a756b9e8e43fc62f0e6243bc876b988d9856a847; original global index 7357.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 5f153587bd20051c2e8206739b7aa63a82f8d36f1f96ee55b702174fc2ae1c61; original global index 7406.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 61c013adcbbdcaa017c9de286a13ddb959bb98ee90330ed2758acfa446eed26e; original global index 7629.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6671d4bf72b78ed793a3b3fa78d8afcb82b69eef8aa96ec8e807c23012974cae; original global index 7967.
def localCycle00070 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, -2, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .triangle 29 2, .gapUpper 2 3]

-- Original cycle 66fe63667b32d69ffd20be00b6035b69cd3a5710eaebd003df3f1f32bb606f67; original global index 8000.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .triangle 23 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6e43877e7fe046699cd2423e83ec298669e5e951fbc6167015676989d8af5681; original global index 8558.
def localCycle00072 : Cycle where
  length := 16
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 6fbec410d411fd91b1c0986d1dffb5addcf770bb8cf39210063568220142494d; original global index 8669.
def localCycle00073 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 29 1]

-- Original cycle 709c01862cdd404b164471f08a94afe87e94588272c098f38642205af504d66a; original global index 8725.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 72b93a678dff8146c09f7e3dfea0aee249d8209a22e4223e603a43bb091bdd1a; original global index 8882.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 74d8ac394d80e1ac2683809d77d78eaeec0adfab5a54b12be660d54851490763; original global index 9052.
def localCycle00076 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 74fb6bb3e1773de6b4969e98a08cd82c6be46d8731da6e0dd2c0552c034ed4a7; original global index 9065.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 76642998a8ef07e06ef39854b693edfbc704a459ec3ffcdcba42ec5bc22439dc; original global index 9165.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 78b854a6e7ff8b26676e1ed53b88aad917a436f2fc2691a45374eab1cbf35656; original global index 9338.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7aadba3a1ce0723efdf98f7e26dc8eb270b3c071e086d20d020d9a16aa9fe169; original global index 9496.
def localCycle00080 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7b0bc13cbd8061190fc2589d6a8c8ccfa82669b57ee0a3813183330c4a53456d; original global index 9530.
def localCycle00081 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Original cycle 7e0b1ec8d394f23da20b83784ff066f3d291a51b487c568afbc1621f6ef2bf3c; original global index 9787.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7ebc1db56e632f1211da17778ff08d9a2508e0cc2768277fbe272f7aa079db07; original global index 9840.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 6 3, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 82584ffff04b1ba3c6e6389934cce9884f3ead5a7a940cd30d842f2e5725f043; original global index 10119.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 17 1, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Original cycle 8311ee679d8903217c0d9f80ae5d5d6db68ee6135342cbba22b5ce16097c873f; original global index 10163.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 83986cae57bdea91fdac6464e214d58b8896ee1bbd986d9ff1f66304b33eccfd; original global index 10216.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8408252c3136aee10580ab0ed9e6d73555bdfc2db2b2ead7982ca3db30bc5b6d; original global index 10247.
def localCycle00087 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .corridorLower 2 5]

-- Original cycle 86d8aae6cd38e8836270a997e6d76aedc166883f50a319029330eee3df869024; original global index 10460.
def localCycle00088 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 4 2, .triangle 11 1]

-- Original cycle 8761c20ae0fbf3676a6a9b97fa714d0de4d82d2d758f397be97bf7d8621c1f31; original global index 10502.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 878dff4cf4c363624ab24ca6c6843e16fb93c5dc2c0bd6560e838172b3f4d394; original global index 10510.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 8796c547d99b764b57badaf27fafc43992a1f337a1eb4c6b5c680b2f15f26134; original global index 10515.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 884ef0625a93301cece78853e888b996532eb407e2bf80d38731834457fa911b; original global index 10563.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 88a3e544cc65a5e5128c434d41703fbbb4a54d83a24b451a72059e95c39b2d08; original global index 10585.
def localCycle00093 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 8c369ed5234554b3e7e46030adad0afc516db5304d58543099de0ea8e7c913a6; original global index 10851.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8c9bb51269ad0cbd8f71e5a88945cd3b035f7eb12058ab9d75cb73ee245c6a2a; original global index 10877.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 8cab59225cca246083044690358a91ec63b58032199016b19e09c5e7df0800fb; original global index 10880.
def localCycle00096 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 4 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8cf848fa3a79bbbe59174d848eef64f1056275463831ac6aeed6202e9ed2ad99; original global index 10905.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 8d524b393c498db70ace05d56b994c194cc32fd38849d9bcb64ca4ad49542b04; original global index 10928.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 23 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9131b84ccb1428c05e6349ff5c3c6a7cb637c407720c9db999ed5c7610282846; original global index 11245.
def localCycle00099 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 1 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle 955204cb239b53ef0533c8061c768e32e62dc260db623d4e3542ee146f9389f6; original global index 11600.
def localCycle00100 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 95cbc7189dd38bac1d9db839ec2b5fcae27070b15fa73309f48a0a32cedf6089; original global index 11643.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Original cycle 95dc099381825bc356f71e51da8ef561e962d150f9d02e62a2e560af433279ff; original global index 11648.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 3]
    constant := ![4, 0, -2, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 1 0, .triangle 15 1, .gapLower 3 0]

-- Original cycle 9701a9bd840141edf894199b1ebd512e438d85c6baea3eb175ddbaaaa472ceb0; original global index 11736.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 988575ab7156437798bec83a51e7ce313c83c1a6384ba16bee77425c96f9e6da; original global index 11846.
def localCycle00104 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 14 0, .triangle 3 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 98aa75620a5058c1e3409d6eaea703ac7538dfad6973dcfa233552a0077d81c3; original global index 11859.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 990ecea472df1c4a1f210acb4b0f087d8239f0a5510c35b7f2367052ee585b26; original global index 11884.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 992290948c9de74b01daca1fa906a4ab90fd740d4201d21236847a680a586a77; original global index 11890.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 9a11720bef56df54b1b44626660f2053023ae212ebcd4db18ea5b63f823cc61b; original global index 11962.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9c7b2b936bf7993b3054207e1a78d77840e96bdfcceee8f6e09ea40442b3d7d4; original global index 12169.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 5 6, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 2, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 6 0, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a1fe57f771416b7ffa9ae228487b313f78ae31303601ccc029a4ead805606111; original global index 12597.
def localCycle00110 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 14 1]

-- Original cycle a2dceb8986a690c2532ba6dfd5d901a0df40562d9c22d61cebc5b2ae1bd1ab40; original global index 12669.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 6 4, .triangle 13 1, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle a3760389d43de84fac5921aa66ceaa6c8c0bc63a6a0b967060e38804962b72a8; original global index 12703.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a5619c57d0a0ffad0404268bc681cb8605e21acbb378c8faeac4df78cf91af17; original global index 12847.
def localCycle00113 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle a75091e9b58d4a0cb48a23851a276ed1d3e0db6d0a28b592c49671250514f8e9; original global index 13013.
def localCycle00114 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle a80ed325acaad30c72bd6872e27e6fdc11f753bc39b96a11214628d1c27cc0f7; original global index 13085.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle aa634f1d1d1642deb07c8a780da4c87c424e2fa5e5d2295036f8628ac9aacaf0; original global index 13271.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle aa9e55ccf0525c46c54b34f835816469332db47b5cd9d30d4aaedccf323e1e10; original global index 13292.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ae27a99a83dfaf96e5ddfb18bee5a387330c4e769484452a0d9a8cc1bc1d61e1; original global index 13589.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle ae8954e95419542c2917ee7e9cade6d10ba54ef0e859ed55446d82e67cdc5b8f; original global index 13622.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle aed0b83bc875f01e5d2a5691f0a5d1e896f125a15476453e23f3a19366f6af1e; original global index 13645.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle af9815117d25b1dc380729ae02ec8888c21210bf6e2150f22e152e0c400c44aa; original global index 13717.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .gapLower 4 5, .triangle 2 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle afa6658a2ae665642e9fbf156a15bf58dc5deddc5ffa9416760dc107e346dbb3; original global index 13722.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .corridorLower 4 6]

-- Original cycle b03c1b4d343087020b86382034c6831388843f98d7f13394842011e1ab969810; original global index 13758.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle b0dfed85b1532f0db35112cc0b05ea59044a0702b9d2ad1aa40d5faf496d496e; original global index 13811.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle b25820b9b86caf56f992481a0a50a90b77ba76066a6acdac20fef0cd341a7dcc; original global index 13939.
def localCycle00125 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b3dae3aedc3e8a64f6e775d65ec5d155d99516c5c8fbd3019c3893dce5c6ae7a; original global index 14046.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle b41d9bf0a61cc1255e445a600a03008e1c55ad4309351e287d77cc8e01de7379; original global index 14064.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 1 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle b4fdcb13896e8197ef94ee7f6455fde98191b3f38c0a074293502249f852e350; original global index 14137.
def localCycle00128 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b6357cae2c6f4de042cc85f7e680ff3e04c24abbd13950a96d024c6fc7b93600; original global index 14232.
def localCycle00129 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b638472502fb7207a3cbc586026b4e865166c3d40842be0ad8c276ef18ba1808; original global index 14233.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 6 3, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle b68d226aa3eedaf46dfe738c1da3ac5292a2ac5cfda8be5a1a816f7bc068517b; original global index 14267.
def localCycle00131 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 2, .triangle 14 0, .triangle 7 1, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b6954f4960bc2a20fcab5e88e4cf4f826c162bf54d8603d567448ad396c5a077; original global index 14269.
def localCycle00132 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 14 0, .triangle 3 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b9b50a89f230189a3104ffdf328064f7d421071f9c1c523146db3c8c32940761; original global index 14494.
def localCycle00133 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 6 2, .triangle 13 0, .gapLower 6 2, .gapUpper 2 3]

-- Original cycle bc2628f268a8976620e117738f4021890672ed6c4a8e0827493e93640aa051b5; original global index 14688.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bc27ab1b3ebeab5ed422d9c5bab5f275dcae1f80672ca72c272a69068b757113; original global index 14690.
def localCycle00135 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 2, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 2, .gapUpper 2 3, .triangle 7 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle bd0e350eb58eb73a827566d8d87fc4297b07db2b722185c3cfed4fee686f913c; original global index 14749.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle bd7e9656b5159af002e0b04971df3863b0745475f2cf91e7fb82e4424a9c9ffc; original global index 14781.
def localCycle00137 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 18 1]

-- Original cycle bd9b40e6eb92b4fd7525a2c671417cb4a83f546ff633dab3797266b173c52a76; original global index 14789.
def localCycle00138 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle bee6037f7e4de4d76221c46e1a4952504460b0b6f05dcb1b102bbc14fe18fa00; original global index 14891.
def localCycle00139 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle c072a53f0e7627de7ad249192d289059ec1936bf76d187d94b4a8d8e2fd617fd; original global index 15022.
def localCycle00140 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c198a8bda6222b99914743574f1f2b0771c086e74bded9a5d5e6d83bb3f520c2; original global index 15122.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c365bebfd7819a49b0961fda9421471a9643bbeba288d49b3746c0d98d35ff36; original global index 15246.
def localCycle00142 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 6 4, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c6a99103b38e1c41f4718cb3df4643133cfa961f204a4b13f5f696ba81ef838e; original global index 15498.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle c7735b2f6c4d8eab6c2722fde6683f43382e43c963151eededc3865435a5670b; original global index 15565.
def localCycle00144 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 11 1]

-- Original cycle c781294450e83b072d240a77a9d433680bcf3a881cee33ca1416404627715815; original global index 15570.
def localCycle00145 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle c7c55f707a3cd94764a3dc9ed8ac7a5fab09dfcb3eb662c35179abe746bdb250; original global index 15599.
def localCycle00146 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c7fddad8a1bd6172a487e8b91148dc1bfd21e61b4daa39a14b3f75af1f446b3d; original global index 15616.
def localCycle00147 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 2, .triangle 22 1, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c8d25a99a23bbdaef1cb8630d770f635fc2e13c6282ed7f8c77bcb9e94e082a8; original global index 15685.
def localCycle00148 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle c91d7e8112667c42788c5687bfe9c15510bb88bcb4e203f7053d5fdf6f0f1b44; original global index 15710.
def localCycle00149 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle c926b167ca9cffa57181dfa03eb670041f134374827ef82dbbb7f90e8d6ec858; original global index 15716.
def localCycle00150 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle ca2476302efe8711d30360ebb1a218d7c2a41dd3dd7ebd918f4f88cb0e2b3219; original global index 15796.
def localCycle00151 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ca2d557057b1a35aa4c8ac0f8c0287d82a5b16f39f717944f793d6fc8aab86cc; original global index 15799.
def localCycle00152 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cc3339fb87d690e173ed093a1d45440ba843e7c9211487b6ff4799f79fc4f7a4; original global index 15964.
def localCycle00153 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle ce24a036106f027202661813a7401f1bcf482d277044226805d4eb9751be6040; original global index 16106.
def localCycle00154 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Original cycle cf29a623ae84105f8f423a806278fa1d666e3062ee7b652343acfcda22f331f2; original global index 16167.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle cf9679979e2e3418d4ab58b554040748f9bdc9155c42f28a1c48d80521944164; original global index 16197.
def localCycle00156 : Cycle where
  length := 15
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Original cycle d04414905b848fc5ad8d7d6fdb54352ed0190fe86587b53498457bf8c1024e51; original global index 16255.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle d0edbc985be8bfb4b6d62349a8139351617f6aaef5edef284fe0d61b261867de; original global index 16315.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2]
    constant := ![4, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 2 6, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3]

-- Original cycle d1aefdb7d85d914217d2b220cd7b0d6e934ad69b9514b47bb920b2cedd7e4293; original global index 16366.
def localCycle00159 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d5966370e274ba62d5a6d04493184b2fea5acce10a95fdff6b0f04ddcdc55e74; original global index 16671.
def localCycle00160 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 1, .triangle 4 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d73ec298aa2e0fd79a49ba88303a146ce16b8e72b5929b9f30e497511c1326a3; original global index 16799.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 6 0, .gapLower 4 0]

-- Original cycle d74338581f3c79c3514b12e0ee0005a9c48707e7abf02387c6054b0c49cf34e7; original global index 16800.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .corridorLower 4 5]

-- Original cycle d7c554ab5437b3c2af910b8b0e3b5e57897f2d7895ed3444bfcce0c0a7f29272; original global index 16836.
def localCycle00163 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d88ff84e8c3ca90d74dbf305c540fcad3b8c51c1a12bbe8e55bc1c9c37500727; original global index 16902.
def localCycle00164 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 6 3, .triangle 4 1, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d8a80f7b22f5cbb29234abe2630483175661cf609b44888386056827a739ab84; original global index 16913.
def localCycle00165 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 24 1, .corridorLower 5 6]

-- Original cycle d964b0acf61ec44405c0a6d3a8ed235e2b6539f01f4fa93af709b1a20ee5b5a4; original global index 16990.
def localCycle00166 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d99aadc961384785a0c0b4e1a21ba85e46ae35211a961abd9b4d81b91c1ae56c; original global index 17000.
def localCycle00167 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle da31917b5a1989e7ab143e0f4be9ea928de3d1ecf6766723c588a412e391f424; original global index 17048.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle dcb1a99c23757a1f31f5e0067a0c61c509ca7e9f9c8bc509e6b48dbb371a8060; original global index 17242.
def localCycle00169 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle dfa59f3f2e0e5849061fdeeb14e6b1c8b6eb423298711390d01ff1215bc97460; original global index 17471.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle dfe1101d87150aed0d95cbbbce2a5f57f29a2478c26a62b71f57106504d3da7f; original global index 17495.
def localCycle00171 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle e06384b1b9d7b0011ce01ac5b5743eb626e62cebea6b338bf799a89b28b52f74; original global index 17541.
def localCycle00172 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle e0a9514a946549ed4c125f922bf2891ce21db76eee9ee3680b9e94886c38b7ff; original global index 17567.
def localCycle00173 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle e1aefa49fd117a4f5e785a02c49678994cbceb030c0a959061ae750284d78b76; original global index 17646.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle e1fd2c42c0eff8cda67ab1a1852be3aeed2f34bfc025b1761bf7113072cddff2; original global index 17671.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle e272f8134a9329af6456663e9c450037645f7fb3fce59f97053ec749ded7b5bc; original global index 17705.
def localCycle00176 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .gapLower 3 0]

-- Original cycle e36844ac09df1c214845ec8dd39aa44962ca4e1e8dcd7476eb2acaf27447eca0; original global index 17783.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle e48c43ccd49463eeac0c0761badc5e353ad4a5e18bf3232c3f6afa2c30166f16; original global index 17865.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle e548f46a137bdd03c020719294f26fe7c621227461e7f2e19a5a1beff5f8f747; original global index 17924.
def localCycle00179 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle e6c25f65d50a66565fbf2492b63a17c492b4c8fd8644b402b772f73bb2100a65; original global index 18051.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e87d60c1b469c324ec0631b65a4548bfdece569babaa9a6e05c1c9c42cde9c6e; original global index 18172.
def localCycle00181 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle e9c8cbbdd22905a9fc29c837b025836d61d2bd595996e63d99d98b4dffe0b85d; original global index 18266.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ead222fdb155038096a5a973b8309dff9f74a232d4236407dd24552b00ea0240; original global index 18342.
def localCycle00183 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle eb23cda9ef973e4f97a7bbf3751def6345a51a3dae06a800fcca9e9e5d8c06b8; original global index 18360.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .triangle 24 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle ec6ac7248faae07d03773b066e9c8a0d8df202cb14c7578b80a9d500b5be3134; original global index 18452.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 4 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ee22b45e5732af14660abe133ddec3116e899aa4aa8c8ef4984f6b95e7fd4641; original global index 18587.
def localCycle00186 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f0a5ffbc4be52f364e8b96c93b43132ae6ee03ce3ce13dbfc3482f0291efc2b5; original global index 18767.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle f0a9824bda98e96d1af51cdb4ae5de3999ca7bcd40212e871e3f122c19ce08e6; original global index 18770.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle f611cb2fe5f13b51bd447cd1e2ae117e159b04a2cf6fb30e5b08feb332c3de60; original global index 19197.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle f81ff735b260327329b67b8ec263295b763627e493336ed61224458941c8e175; original global index 19348.
def localCycle00190 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle fad44ae3df13abe2856eb707c919a7f69ffa70e550ae9af3fefa8bb47e0f319d; original global index 19571.
def localCycle00191 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 4, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle faf8d7c385e49def813afb5d28c72cd7f84fccde7f464d9b12f5490bb1a102be; original global index 19587.
def localCycle00192 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 6 4, .gapLower 6 3, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle fb20096b21cc982bf4bacd3624855ef122278a06b8ad07212397a249c5baade4; original global index 19604.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle fca69903d14bbfbd6e8bc3f8c9430e720970c9a2422f5434bd7deb3bc18efae9; original global index 19740.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .corridorLower 2 3, .thetaLower 2]

def library : Library := fun id => if id < 97 then (if id < 48 then (if id < 24 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))))) else (if id < 36 then (if id < 30 then (if id < 27 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))) else (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))))) else (if id < 42 then (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))))) else (if id < 72 then (if id < 60 then (if id < 54 then (if id < 51 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)))) else (if id < 57 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))))) else (if id < 66 then (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))) else (if id < 69 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none))) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))))) else (if id < 84 then (if id < 78 then (if id < 75 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))) else (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))))) else (if id < 90 then (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))))))) else (if id < 146 then (if id < 121 then (if id < 109 then (if id < 103 then (if id < 100 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)))) else (if id < 106 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))))) else (if id < 115 then (if id < 112 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)))) else (if id < 118 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)))))) else (if id < 133 then (if id < 127 then (if id < 124 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))) else (if id < 130 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))))) else (if id < 139 then (if id < 136 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)))) else (if id < 142 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))) else (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))))))) else (if id < 170 then (if id < 158 then (if id < 152 then (if id < 149 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)))) else (if id < 155 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))))) else (if id < 164 then (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)))) else (if id < 167 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)))))) else (if id < 182 then (if id < 176 then (if id < 173 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)))) else (if id < 179 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none))) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none))))) else (if id < 188 then (if id < 185 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)))) else (if id < 191 then (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))) else (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![3, 5, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 1, 5, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 92 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10368)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![3, 5, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 1, 5, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 1, 3, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 105 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10369)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![3, 5, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 1, 6, 3, 0], ![4, 2, 1, 5, 3, 0]], proof := .tail 56 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10370)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![3, 6, 5, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 6, 1, 3, 0], ![4, 2, 5, 1, 3, 0]], proof := .tail 28 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10371)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![3, 6, 5, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 2, 1, 3, 0]], proof := .tail 170 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10372)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![3, 6, 5, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 1, 6, 5, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 2, 1, 3, 0]], proof := .tail 183 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10373)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 3, 5, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 6, 1, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 6, 1, 3, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 121 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10374)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 3, 5, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 1, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 29 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10375)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 3, 5, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 1, 5, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 22 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10376)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 3, 5, 0, 4, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 1, 5, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 177 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10377)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 3, 5, 0, 4, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 1, 5, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 172 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10378)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 2, 6], ![3, 5, 0, 4, 1, 6], ![2, 5, 1, 0, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 6 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10379)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 2, 6], ![3, 5, 0, 4, 1, 6], ![2, 5, 1, 0, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 162 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10380)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 6, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 1, 0, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 93 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10381)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 6, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 1, 0, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 93 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10382)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 6, 4, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 1, 0, 6, 4], ![5, 0, 2, 6, 1, 3], ![4, 2, 3, 1, 0, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 127 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10383)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 6, 4, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 1, 0, 6, 4], ![5, 0, 6, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 78 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10384)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 3, 1, 2, 6, 4], ![5, 3, 0, 6, 4, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 93 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10385)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 3, 1, 6, 2, 4], ![5, 3, 0, 6, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 0, 1, 3, 5]], proof := .tail 93 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10386)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![5, 3, 6, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 38 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10387)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 1, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 178 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10388)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 1, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 190 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10389)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 68 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10390)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 135 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10391)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 3, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 33 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10392)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![3, 5, 6, 0, 4, 1], ![2, 6, 5, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 2, 6, 3, 1, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 0 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10393)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 5, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 180 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10394)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 5, 1, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 1 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10395)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 5, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 30 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10396)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 5, 1, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 59 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10397)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 2, 6], ![5, 3, 0, 4, 1, 6], ![5, 2, 1, 0, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 24 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10398)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 2, 6], ![5, 3, 0, 4, 1, 6], ![5, 2, 1, 0, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 34 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10399)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 6, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 1, 0, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 3, 2, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 187 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10400)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 4, 6, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 1, 0, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 3, 2, 1, 0, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 89 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10401)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 6, 4, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 1, 0, 6, 4], ![5, 0, 2, 6, 1, 3], ![4, 3, 2, 1, 0, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 171 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10402)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 3, 1, 2, 4, 6], ![5, 3, 0, 6, 4, 2], ![5, 3, 0, 6, 4, 1], ![5, 2, 1, 0, 6, 4], ![5, 0, 6, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 40 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10403)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 3, 1, 2, 6, 4], ![5, 3, 0, 6, 4, 2], ![5, 3, 0, 6, 4, 1], ![5, 2, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 187 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10404)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 3, 1, 6, 2, 4], ![5, 3, 0, 6, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 0, 1, 3, 5]], proof := .tail 23 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10405)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 3, 6, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 1, 0, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 23 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10406)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 1, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 118 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10407)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![5, 3, 6, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 1, 6, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 41 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10408)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 175 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10409)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 175 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10410)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 6, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 87 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10411)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 6, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![5, 6, 3, 0, 4, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 169 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10412)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![5, 6, 3, 0, 4, 2], ![5, 6, 3, 0, 4, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 41 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10413)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![5, 6, 3, 0, 4, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 87 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10414)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![6, 5, 3, 0, 4, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 52 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10415)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![6, 5, 3, 0, 4, 1], ![6, 5, 2, 1, 0, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 44 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10416)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 5, 3, 1, 2, 4], ![6, 5, 3, 0, 4, 2], ![6, 5, 3, 0, 4, 1], ![6, 5, 2, 1, 0, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 181 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10417)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 57 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10418)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 66 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10419)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 176 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10420)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 129 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10421)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low6 (![86, 110, 15, 137, 5, 8, 182, 69, 3, 157, 85, 166, 134, 25, 42, 64, 184, 160, 67, 123, 153, 131, 102, 165, 185, 167, 194, 108]) }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10422)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low6 (![54, 145, 50, 137, 5, 8, 182, 120, 11, 94, 85, 166, 109, 4, 163, 27, 186, 51, 158, 96, 65, 125, 102, 143, 185, 167, 194, 108]) }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10423)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 76 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10424)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 80 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10425)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 46 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10426)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 46 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10427)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 104 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10428)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 136 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10429)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 1, 3]], proof := .tail 132 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10430)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 58 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10431)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 136 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10432)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 1, 3]], proof := .tail 152 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10433)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low6 (![20, 77, 53, 119, 128, 8, 182, 141, 116, 193, 193, 193, 193, 126, 47, 79, 79, 79, 130, 155, 103, 82, 188, 90, 164, 60, 98, 71]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10434)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 136 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10435)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 4, 1, 3]], proof := .tail 148 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10436)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 0, 1, 3]], proof := .low6 (![112, 13, 73, 36, 48, 88, 91, 168, 115, 83, 19, 19, 19, 133, 12, 111, 35, 159, 32, 55, 97, 49, 192, 45, 70, 144, 142, 17]) }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10437)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 0, 1, 3]], proof := .tail 74 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10438)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 95 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10439)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 6, 0, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 61 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10440)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 6, 1, 0, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 107 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10441)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 139 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10442)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 6, 0, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 179 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10443)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 6, 1, 0, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 107 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10444)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![6, 3, 4, 0, 1, 5], ![6, 2, 1, 0, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 75 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10445)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 5, 4, 6], ![2, 0, 1, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 63 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10446)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 5, 6, 4], ![2, 0, 1, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 43 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10447)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 140 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10448)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 21 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10449)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 191 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10450)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 2, 4, 3]], proof := .tail 106 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10451)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 106 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10452)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 1, 4, 3]], proof := .tail 161 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10453)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 4, 1, 3]], proof := .tail 39 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10454)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 1, 4, 3]], proof := .tail 161 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10455)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 4, 1, 3]], proof := .tail 39 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10456)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 4, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 0, 1, 4, 3]], proof := .tail 9 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10457)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 0, 4, 1, 3]], proof := .tail 113 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10458)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 0, 1, 3]], proof := .tail 138 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10459)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 26 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10460)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 174 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10461)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 6, 0, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 150 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10462)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 6, 1, 0, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 124 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10463)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 0, 6, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 26 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10464)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 6, 0, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 114 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10465)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 6, 1, 0, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 122 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10466)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 2, 5], ![6, 3, 4, 0, 1, 5], ![6, 2, 1, 0, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 173 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10467)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 99 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10468)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 100 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10469)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 62 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10470)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 146 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10471)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10472)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 147 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10473)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 10 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10474)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 14 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10475)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 101 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10476)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 18 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10477)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 4, 3]], proof := .tail 84 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10478)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 4, 3]], proof := .tail 117 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10479)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 136 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10480)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 4, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 136 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10481)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 6, 4, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 4, 1, 3]], proof := .tail 151 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10482)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![3, 1, 4, 2, 5, 6], ![3, 0, 6, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 4, 1, 3]], proof := .tail 101 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10483)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![3, 1, 4, 2, 6, 5], ![3, 0, 6, 4, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 4, 1, 3]], proof := .tail 152 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10484)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 4, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 31 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10485)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 4, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 154 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10486)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![3, 1, 4, 6, 2, 5], ![3, 0, 6, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 4, 1, 3]], proof := .tail 156 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10487)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 0, 1, 3]], proof := .tail 189 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10488)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![3, 1, 6, 4, 2, 5], ![3, 0, 6, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 0, 1, 3]], proof := .tail 81 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10489)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 16 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10490)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 6, 0, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 72 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10491)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 1, 0, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 7 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10492)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![3, 6, 1, 4, 2, 5], ![3, 6, 0, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 149 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10493)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![3, 6, 0, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 1, 6, 0, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 2 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10494)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 3, 1, 4, 2, 5], ![6, 3, 0, 4, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 1, 0, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 7 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10495)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (10368 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 10368 ≤ id.val) (hhigh : id.val < 10496) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 10368)) = true := by
  let j : Fin 128 := ⟨id.val - 10368, by omega⟩
  have hsum : 10368 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (10368 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard081
