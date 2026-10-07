import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard179
open N4R2RowDataReplay

-- Original cycle 00638dc0837b20af45db1c60f3d7889fc2512a8095fc5e051e593fc5a3c9a280; original global index 35.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 02789af3875b3858b9761bf810f42f32c55b02adc4e22a2c0022859bf8c3b51b; original global index 194.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 02833e8410033596ecd29ca3be6c207dc1cd2674600a66efa20fea2b4cc33a45; original global index 196.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 0595de2987cec66cd8c5ece88a19658066015792855ca1ab5e21304630335039; original global index 462.
def localCycle00003 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 6, .distance 1 6, .theta 1]
    constant := ![3, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 27 2, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 0873e1897e79fbfcd1819ad8de1c6e9ca6e66a560dcc5185f1d1ff7c5b9b18ca; original global index 675.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .gapLower 4 0]

-- Original cycle 0940c902d8b2a5d1dc8f1c4b0352555c9aff2cca0bda0ac0974b1b1f0fc54de0; original global index 740.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 0bd6b004d3933dcebca0be07ba29885efcb43f415b626ca4a1f241df69cd199b; original global index 942.
def localCycle00006 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 28 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 0dbca9e30c5a879ab9771f6c3465f3fe30d8ffc3f3e3f0db077bf2aa5db5dd87; original global index 1087.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 6, .distance 3 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 1144efea9a0263179446abb25ffea39dbefe4cb24abfaec433adaae9c2e6f07c; original global index 1372.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 15a81751053e30002942a649e0de165b835a8070a645726f3c687f938e543434; original global index 1718.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 15b163739f851908b163d344415278ad72ae831d45668b07cbd141d587992fd9; original global index 1723.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 1cec3c76e4471af9e1f7a97db64c5fb985d2d7560e9385038e496f785af6e1dc; original global index 2230.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 1e18848b1ad4d4df95469886e0bc2e496732419d08849ed8254e5c9f885665bd; original global index 2313.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 223c211b36071d3e680e5997fccfb44ff75a4a878eb195b6978ecb6972fe34e6; original global index 2622.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 22f8e5754b2ba466704010095c2ad5b5d6da69024c99e4e471b10381abd8353e; original global index 2682.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 27 0, .triangle 21 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 252978e0f6e4f844178edf131c5d0b4778dbaa1013e484e2b6159f1079738f8b; original global index 2856.
def localCycle00015 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 298560b82c5d307f2e1312c84ebaa394fce77038caddcf03098aa5690822a038; original global index 3163.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 29dd9f23dd95bbd780ce82a31bf658ac78f3dbea665a65140cc96af7b982796a; original global index 3195.
def localCycle00017 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 2cdbe68e3fa4c7ae03b44517b9199a08800b15cd34cdd356fc5e393190f53ed5; original global index 3426.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 13 2, .gapLower 6 3, .triangle 18 2, .triangle 21 1, .gapLower 6 0]

-- Original cycle 30a210c1c0c318cdc96cbd3612c436b4185e62bc66777a282d9599256104bd50; original global index 3711.
def localCycle00019 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .theta 6, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -2, 0, 3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 21 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .triangle 7 1, .triangle 28 1, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 318b7ecf798ae4b7f4e5df293d9cf59d70be51b3c7e18cb1a2f007fc89ee7200; original global index 3779.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 6, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 21 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 324677cb1e15d6bf3d03e63414c6d69d65d28f22f508ddabb9b142aa28af37dd; original global index 3838.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 2 4, .distance 1 2, .theta 2]
    constant := ![3, -1, 0, -1, -2, 2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 21 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 12 0, .triangle 6 1, .triangle 16 0, .gapLower 2 0]

-- Original cycle 338813396f9c69e5af97d931d89a9e4b3f0c6cbe3e3a230d369806578ca971d5; original global index 3942.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 1, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 33b94f6ab3ef36446474ff666e32d3902fa5f594ade10ecb35d95ea2ef9cd8e3; original global index 3960.
def localCycle00023 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 35742b9578cc98adcf00ab2589259155277e92e966e91ad0eb06a90b897a3017; original global index 4096.
def localCycle00024 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 11 1, .triangle 33 1, .triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 35deea14b2a3a44dee47c1b29e018b3af783de9fc267ee31d52a9cc2d76c3c4a; original global index 4133.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 369dc78972a2f4d9f3d78dfd30c4ff06873af5444142fefde6dd96b2d1f0edfd; original global index 4196.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 3793fac1ca5c4da8ff61477a4f9af0cbdd399b5810cc54296da31f32c4281c6d; original global index 4275.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 37df835c51a4792db78e887d2cc94bc68665275653ec8b4360a327b1d661cdd5; original global index 4294.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 11 1, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00029 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 3977a0079bf2120f4762a27cfe4938619ddc8b7995c21783c806ab7381267d6a; original global index 4428.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 3, .triangle 11 0, .gapLower 6 2, .triangle 18 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 3c23844bc917fc64039640454ceafc2aaeb530e844968763b3a51b86d185ca2a; original global index 4662.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 3daaf86528d7f60fecc402848d919f39a5c01cdc9529167e26f84d1b5849672e; original global index 4776.
def localCycle00032 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 14 0, .triangle 12 1]

-- Original cycle 3ed3865b761f8ed3ecda9c9377eea83c2bbc0499b94f1256c4072494e4055380; original global index 4856.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 3 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 6 3, .triangle 27 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 42086585f8ee57816155f707f499d03f2e5e76b8820e1eda26e162017cc40d84; original global index 5087.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 30 1, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 43fa7d98dcd878be60ddb5787094cb27dbffc5ab2ab2f67471026d2cd2e0b33a; original global index 5261.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -2, 3, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 0, .triangle 19 0, .corridorLower 1 3]

-- Original cycle 44bc28f4dd28f20b5011da9aa6544dac6a633d79455784d465b560552a439dfc; original global index 5327.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 3 5, .theta 5]
    constant := ![3, -1, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 8 1, .triangle 18 2, .gapLower 6 1, .triangle 33 1, .gapLower 5 0]

-- Original cycle 462c1242474aa9be58738084755099fa76cda00d76f29488a911dc0ee23faad6; original global index 5430.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -3, 3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 19 0, .corridorLower 1 3]

-- Original cycle 47f1559f3fa7e1a2aeea4796fb49dfe6c42d8e8eab405da631bc7938be56512f; original global index 5569.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 3, .gapLower 6 2, .triangle 21 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4a97387d5d73782fffd2fbe982dc3598c456957ca428f432b57e4ba457df65b1; original global index 5787.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 4ba4b0df73725c72ac7f0335f42ff3dcb9cf63e28516ce443ce9b360e147b81b; original global index 5870.
def localCycle00040 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 27 2, .gapLower 6 2, .triangle 21 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 4e81e591a96f4f1b8c1d1727780ceaa7a641f96dc46c12dd6b056f9312d75a31; original global index 6100.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 4ef6385a1c283ee1ea440910abcc45afd1992daabcbf3dcd1686ff8c26bdb230; original global index 6135.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 1, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 4f9fd991ebd572026ff753401d7712a4fb4117712f411a79a0709deba6ed769e; original global index 6182.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 50b86e5d0dd36274694fcaf48487ba776c74ac824f42cc5307f0878216963322; original global index 6266.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 50efc6d13b8a4951105de4e1de1bfbd4974d89bd1b7ce4fb3212216958b61018; original global index 6287.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 3, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 5157bbbd95cc67b9c27ea31f7f2a6c030517445c0524379567fa7fc287b2da4a; original global index 6326.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 516a241b439fc2df10b1b614117040896d877450d1ceacb72de19aff0ae1b969; original global index 6330.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 51b2433900584d289fbe76b056f359f61033d02e7ebc23dfb25a1700c5abfac5; original global index 6360.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 53582e7823d819c9eeac2b576b2505f820dc557c6b37e2e2f13c51ae2039f1ad; original global index 6481.
def localCycle00049 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 55498e92a236471cb4f8ebfcb92d96e888979010431da33b3fac77b4c45d2b1b; original global index 6604.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 55535337ae05d9694e373121928714669eb2cf0734a19e07065860c6181f23a9; original global index 6607.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0, .corridorLower 1 3]

-- Original cycle 596a04b18072702307f6a67fd4af5b4f7baac962ec0a627089b7640def6abbec; original global index 6945.
def localCycle00052 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 1, .triangle 18 2, .triangle 21 1, .gapLower 6 0]

-- Original cycle 59a6dee0b6fd64dbda19bb54516b3ddf6b758ad1f4b31d4500c6e4255913c22a; original global index 6974.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .gapLower 6 3, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 5a44bf134757bd85e0d0a4f53e2461d511431a13bc7a91aa346f0a99418bfdea; original global index 7023.
def localCycle00054 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 2, -2, -2, 0]
    coefficient := ![1, 1, 0, -1, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .gapUpper 4 6, .thetaLower 4]

-- Original cycle 5abe9e24f0b705d377e8ae62960643b16de229e988867afa4ff8b70b3805a6a3; original global index 7066.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5bf8ec6a7d73975c7b028323436fc95e69e5f14d01565ffb870baf11d014c398; original global index 7156.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5c25a8da6f36b2cd5ca4ba9a8a4f2cbd718faa0c131a836b844d619b01b61f19; original global index 7172.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 28 1, .corridorLower 2 4]

-- Original cycle 5ef524325791f9ac5e1d351d6f234510d99edc9b37583c2398ea1494d78c85e9; original global index 7393.
def localCycle00058 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 27 0, .triangle 21 2, .gapUpper 1 5]

-- Original cycle 5f1a2f490153fee0810c8863814bf4412b537a1ff6a7fb83c502a4899ce6eda7; original global index 7407.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 5fa14f83bdcb7b76ee94c9883cd4c111a6623ff3ba7ef8656a7e616be5244939; original global index 7449.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 3, .triangle 18 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 60d8939564add0783e1cb1a77bebe22f6ca2222a562b241aead39a64e33800d3; original global index 7547.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 610574bd9e9943800f7b6255bb32b4dd58292006dab6b0e320a4c5438cb9564a; original global index 7562.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 3 5, .theta 5]
    constant := ![3, -1, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 8 1, .gapLower 6 2, .triangle 21 1, .triangle 33 1, .gapLower 5 0]

-- Original cycle 615ff9f7d325309dde418056a99a19a0df03843ac08d168ff1a1797166412ad4; original global index 7594.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 21 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 628d518084eedf935260512a2b13df17b25dd33ba452afdf0486dce7053ed909; original global index 7689.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 6350b4b9ca93c407558e81627c5cf7abfda2efa2a8ea804eee75f7e6c163a1db; original global index 7750.
def localCycle00065 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 669be4139dfd6a43f0269f9d2e49d54d6215acff670b9e6f53a407cf83569c69; original global index 7973.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 68ceb683ec0766fefdd5589505f89959620d598656555446f44a8d8fb613d0fb; original global index 8151.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 0, .triangle 30 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 68dee03b7400027bcfad84fc624bc53338ef676bd692f608c3c81d535f2ca1be; original global index 8160.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 6 3, .triangle 18 2, .triangle 21 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 69178c6071132142a425d2f2712fd723623280937eb95a06cf56df800282424a; original global index 8174.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 699f201daf7cc44a983dcdb0f4d9e4972dd3d78535d4bbe000faaaefaa60e7ef; original global index 8219.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 6ad1bc462fb233945ee1f7092171830414cad06be725b63f4d0b8691ae5068c3; original global index 8316.
def localCycle00071 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 3 5, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 1, 0, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 1, .triangle 14 0, .triangle 10 1, .triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 6aea1ef5c771e146e8b3ac01cd63a39b6c4736081627c03c2be6dfb53204934d; original global index 8326.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -3, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2]

-- Original cycle 6bea39d027be797223755769a853885de1862ce8fe419c3e909492315160b519; original global index 8409.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 70bbf625bb2ea2907cc5fd609782a2587d323d476d6dfc817aaee25fcaff3d0a; original global index 8739.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 75060e6341abd743c70ab7a20ee0382bf33071d97ea2cc76cb7531b0534a222f; original global index 9069.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 7520f11c93348c63018e5c832f0275bd49545bbe730ba4b8a72091e3cae05a96; original global index 9077.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 1, .triangle 18 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 76f198d598b0bb3309cace2f1ff3b7846a0d7af1c4a07c75ffd12af405db16f7; original global index 9206.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 7921cc0c3587aea654fb6403937b9f0ea1f443d146054722bb0298716df22a27; original global index 9374.
def localCycle00078 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 7ac2398bbbc85bf12ba1e685897db29eeb0820eecdf76b41368d72dfba873280; original global index 9502.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 7d3014e8dab98a7c86a5f9752aead9bc5130fdde4ae8a3ccd0a87783f25d16d0; original global index 9703.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 7dc0abd35458d4a8a2098cf49fa5748d867a5dffd102e9d4144a7bdf72294a6d; original global index 9763.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 7e27f0f832eefe75dd7267375a7eef16a8727da2a5d4e2558751eb3a40fb1eb9; original global index 9800.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 7e462739f56bbc4ef93307596a64d23b7d2ef4116393db3449521ca2237fb932; original global index 9808.
def localCycle00083 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .theta 6, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 3 5, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -2, 0, 3, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .triangle 10 1, .triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 7ee813df953a8059b225852d84a9b15725d4db76847bb0214644b2a52fea4309; original global index 9853.
def localCycle00084 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 3, .gapUpper 3 5]

-- Original cycle 7f334bf1ef9690cf921e8abec131d322187d62b7580f62aaca5b9090207312bd; original global index 9867.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 3, .triangle 21 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle 80130c79e759f728ba0daeb29287da6159b10d934de02e93e5750ecf35e677e9; original global index 9932.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -2, 3, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, -1, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 21 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .gapUpper 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 81385fd45bc329080fa0fac4258b62716f984f5186ed1bdfac32e50546965ae2; original global index 10029.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 838a62479f137205a57316ff5cad30eb5fe9613ad41a8b571949bc206422cb33; original global index 10208.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 84c14b4799d4a4541740e2b33ca4d5acd2c4374ed5ee228edb679f6533fcdb40; original global index 10307.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 5, .theta 5]
    constant := ![3, -1, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 11 1, .triangle 21 2, .gapLower 6 1, .triangle 30 1, .gapLower 5 0]

-- Original cycle 86974aeb86c19e7d2ac5a110456b04ddefa03cc282c4f7604b90649403c17cd0; original global index 10436.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 8708ee65e4903455e0def8d450230b799b0444e86094fc1ce431c405552cf3e4; original global index 10475.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 870f792b95ee7713430a93d10892b29e16fbc7e6fa7846992d0d87c3f02b30aa; original global index 10479.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 5, .theta 5]
    constant := ![3, -1, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .triangle 18 1, .triangle 30 1, .gapLower 5 0]

-- Original cycle 87d72e83a6e71d8e118b32aa8f38b03f4d952331e3d824cb16574f2d7039ffd9; original global index 10528.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 11 1, .triangle 21 2, .triangle 18 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 88c874eb5f9ac80bb2fadcad0d8c153f1e6d00b5a92a440f7e05dbf76c8badf2; original global index 10597.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .corridorLower 1 2]

-- Original cycle 8acc673a8973760cdf2081932a98541f9100873d05569f27c93bd416f3242fdb; original global index 10755.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 8e19ce58ab32d95da543428a7d817c65f18b80409141487bdf26ae86e03ad270; original global index 11006.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 8f88ef9a4104a15a9b99d91a674b7d9d57eefe3bcb8b53e57715c0839df4efff; original global index 11107.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 9034c54fc071a9de676df54af0f0a8edcaa1929bc833ad01c759f5ee07601ca7; original global index 11164.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9350e2157b4c7950652db12d46426a9748b7d5d89e7a9d05f39b9e0e69e16e01; original global index 11423.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 99f29a9d965fa1261acdeb0c54cbed347580fb6764982ff322ee20b002fe5701; original global index 11951.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 9a432e57cce88c6cc61ddfa0b2771913f8c40c0ed2f14fac2f616923ce24a810; original global index 11987.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9a4499f81899506798bab69a53ba822a41584a1c4b6a3000da695a516f4d3eab; original global index 11988.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9add0c35ac94f8438b8bae503b6d87e9080af8735c169cbfb013d4bc651f8b7f; original global index 12034.
def localCycle00103 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 6, .distance 1 6, .theta 1]
    constant := ![3, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 27 2, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 9ba7c5222f88df12c058deaedece436d470c1355bf208a6e2065c7a8781c6e33; original global index 12108.
def localCycle00104 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 9efa841ce9e2e1893016219ffd823cb5e5bc0148550714cde2ad57d1ba6163a7; original global index 12380.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle a0df4e93b0115b41e0d224fae2898f65f838928215f5b82f05e8e74938891aa8; original global index 12513.
def localCycle00106 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle a47c33631d3795e90de370f2c3fb3ea3b26be0265a7e7052cd74625f237169b2; original global index 12787.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle a4c559ed5f70a59986e0d45c777effd05cf637b919fec7f982671d78f7a67ab3; original global index 12805.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle a6b84b72799d90a3a507a373911a3835fd6798916dae60e421bc0c70ce2a471c; original global index 12951.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a713bbe8c1d8f07b115b000202af27b66782cff7c4951410a68e307b052b4fc0; original global index 12986.
def localCycle00110 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a9becc77dae314109ecc5f011a26e20decc4adef3d5b030c712cf065ea76bbf7; original global index 13214.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .corridorLower 2 4]

-- Original cycle a9cec9ea07226446aedd666abb143dab55c96e2fd7838d903ec2b054e8f3350e; original global index 13221.
def localCycle00112 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2]

-- Original cycle aa11df963322a229e7341a9a90371923a2603bf045686ad16b8c685992ccf064; original global index 13240.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 3, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle aa1f6f67fa0971824fb7240eb99a0cba30d76b22b903539636ea554781c80486; original global index 13247.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 1, .triangle 21 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle ad69bd633c6e78b3fe02587e4fe7a1a267d88735800e9cc1f4a8a5d05dadc061; original global index 13528.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ada11d08af547d4ce0df172456f8757147b137c15dc78b3e62684ec2060cd11a; original global index 13552.
def localCycle00116 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 13 2, .gapLower 6 3, .triangle 27 2, .gapLower 6 0]

-- Original cycle adff1e9bc3a34055677ba3586a90f08bd009d09b41a958eec5318fd0f24665af; original global index 13574.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2]

-- Original cycle af0b259fca486982622289b7fff67499733e5746f733fcccf3baf65e8f526e31; original global index 13662.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle b017b1523d54eff31439fe2ae68713e954812720e891b37c75d754b7100b2f9d; original global index 13748.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle b35b0ba6c00eed1a1c83a78eec2d9f92c4dca02eedb298da2733e588cd5a6e48; original global index 14016.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle b5a8f3986e18c2d339d55b439538c7946283e7866e7e28381df2d5af9c25c0cf; original global index 14195.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle bbdf55ad2c330fcd1bcf792c17b5e5ea43d11fd3da3519f983340c4aa313b69e; original global index 14675.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 27 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle bd0976ad1e5223406d06afab717d9b1d923507d979e3e9179468c5edc2c7180f; original global index 14745.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle be29c54c8b7810fe7b35840a06f2ec4a12347721747bb3dbf30b650da0359b3f; original global index 14831.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle bf3067ead69f1cc8e4a77898ddf831660bf07b0f3abd13ac06c6257c5daa4490; original global index 14921.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c5173e68bf4b1ce8910ca1a51455738d47e5ab390bd63bb434acf9aaa335e23d; original global index 15378.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c71499b413d779490cdf4a7bf464fe112f82e55a660837edc7c7ba589e3145dd; original global index 15534.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 19 0, .corridorLower 1 3]

-- Original cycle c801e46ba29761cf0cfb7ec47be59d9404710ee8297a757267ae59bcb5c460db; original global index 15617.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c897e874a3531c706578098b6fb78bd8518751bcace338b5aae46cdaef648f4f; original global index 15668.
def localCycle00129 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 33 1, .triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle c8ec626fcd2437ccc042fdec9e0e57c645cb3f36cb5d4a1a5ac87813d80b53b6; original global index 15692.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .theta 6, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -3, 0, 3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .triangle 10 1, .triangle 20 0, .corridorLower 1 3]

-- Original cycle cb0496a5b475617273ace8c28069195c6be55d660b6faf9da35e3637fa636ab5; original global index 15863.
def localCycle00131 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle cb40660610011407b306483b1e9cae68fe6f50cf806ebc34042a0da4d2c5553c; original global index 15875.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 2, .gapUpper 1 5]

-- Original cycle cc296b6fd778bb9fe8253dbc4253748bbf51019d4bbf400b0493e037655fe50d; original global index 15959.
def localCycle00133 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 13 1]

-- Original cycle ccd50d683452b99c40eabe1c29cd6f8821dd4388428e3a1d00fc9396a9b9117e; original global index 16008.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 21 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle ce06a823acb659c36e8c9d808aa9678075383babcc022e36059992691251a6d7; original global index 16096.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 6, .distance 3 6, .distance 1 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 3, .triangle 21 2, .gapLower 6 1, .corridorLower 2 6, .thetaNext 1]

-- Original cycle ce90bfa52912c912ff3bbd9cc8d03163ff915fb52452e157ef23884ea5c144c4; original global index 16132.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle ced5f7f1516934980b21087dac9b16203852bd973fc83a5c4db43a45846dd8c3; original global index 16144.
def localCycle00137 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 8 1, .triangle 30 1, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle cfe84d1b625f19771b7c68c256cd0830af22bcc82fc4ebda43784795cd68490f; original global index 16223.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle d224cf0e4c22e3bf708e2e4543beb9e9bfd37976c25bf71c9cab3258afca6542; original global index 16398.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 2 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 1, .triangle 21 2, .triangle 18 1, .gapLower 6 0]

-- Original cycle d5d3d11d56434b6723fbe7230570bdf7d9edcd348bc182771723ac88d289d44a; original global index 16690.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .corridorLower 1 4]

-- Original cycle d79cec62a9d12116699d00a8ce9e472a7ac5e2f7a3eefbe9b18bca9f2774c9fb; original global index 16826.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2]

-- Original cycle d8e736fd8b791d4c3df07cb905fc8f2939bd02c0c26b190b76d4f1204f773031; original global index 16938.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle db749132c7e57e8738b1fa326620a29e5b407c523dc583ce5c80f324d5652f17; original global index 17154.
def localCycle00143 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle dc115bb1f8657f567fa9c2bc68743ba040803e78137a48fd47f1f6c38da88cbd; original global index 17201.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle dcc121cafe4da55be1f7840c2437c713afb87272b5a73bd2b00c171163cf85da; original global index 17248.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle df7c232c10558e896b50abaa2185bbdbcb8604588d528fa357f6dd3671dbad4d; original global index 17464.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 21 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle dfc8a09ce8951818af0ef40dd3f8eb983ad232cb1864347b37f5819131d4842a; original global index 17484.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle e16c19ce0407eef8dc302e7086dd91ecce36d7fbdc16f680ef8c328674f9303b; original global index 17627.
def localCycle00148 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 14 1]

-- Original cycle e2fcc7a24cb8800584409c4a023a7a753b6931a184b3ed23f871d71bc2400ff9; original global index 17752.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 8 1, .triangle 18 2, .triangle 21 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e5f35d1486b17de5bcfd6f6e516b5503556c5e701fd484028e1264dbc7d75b72; original global index 17992.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e9553d27e748575cbd6470cd6aacf023a3137722954313c109258347f9f8400f; original global index 18236.
def localCycle00151 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 14 0, .triangle 12 1]

-- Original cycle eb8177ef5bbee19a86545a3414859cd363c37ea2569f7539124e4b07fe6dced1; original global index 18379.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle eed259cce8b89130a0bd5f34049d3ea83744fcf4d3eeab4a1ff7bcb5fdb0df8e; original global index 18640.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 15 0, .triangle 16 0, .corridorLower 2 4]

-- Original cycle ef38c077a28f60a14546a5c3171fabc051c9b3eb20d7ce23ff4f79794e6610a7; original global index 18665.
def localCycle00154 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .gapLower 3 3, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle f16e803b811ca2bc2feaa54ea4dbfbd3300e7a29669f1bdd35bf30bfee73d40d; original global index 18823.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 15 0, .triangle 16 0, .corridorLower 2 4]

-- Original cycle f466991211d114ad6e09643421d914eb68c41b1c25a27f45b9d30b2c807f66af; original global index 19053.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f4c5bef1baa947ead08cf1285681f9cc1cf4642d17e03440e5fef7a058922155; original global index 19080.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle f517b448ba01e71a725e8ed4d0b494dac64f086e08c976625fbb8e0ad6a5eef4; original global index 19106.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f57a884c5076e780dc94aebd31a1ec18b8ddd9c34392c433e945bd6ce0d8a8df; original global index 19139.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .triangle 8 1, .gapLower 6 2, .triangle 21 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f5dbc9f90cfa53cfd9541e45ebe84223a963000e438111f43e033c9ffd4c7de5; original global index 19183.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle f663ef2c1288abc78bdf94373515092f442da538f53414fb3a8ccc48b5f314f8; original global index 19220.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f6e01659b11f90e06b263b8dc97de2a3e13d4fce59b316e1d1b8e6a8fea479cc; original global index 19256.
def localCycle00162 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle f81d6d0702fb71ed6e99d0082c3484ccca4e686cd609037c8992a3bd12636304; original global index 19345.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f86bd1da00f92233b7fcf4eaf1ec9336d6c247083ae73f5bb513a00f5be3e065; original global index 19375.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f98889a2da40ce2c0055485598d3f18a46be817bf53d07a37a8fac0a191ae625; original global index 19454.
def localCycle00165 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 3, .gapUpper 3 5]

-- Original cycle fa469b1d403e42168a5117089829a7f7aa88dd2ed088bf3de39a24c91027d237; original global index 19520.
def localCycle00166 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 0, .corridorLower 2 4]

-- Original cycle fe6f45358a970f0edde6c2cc049243287ee4e9ef984ad50deb2efd622d50e2e7; original global index 19890.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

def library : Library := fun id => if id < 84 then (if id < 42 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 31 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))))) else (if id < 36 then (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))))) else (if id < 63 then (if id < 52 then (if id < 47 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))) else (if id < 57 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))))) else (if id < 73 then (if id < 68 then (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))))) else (if id < 78 then (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))) else (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))))))) else (if id < 126 then (if id < 105 then (if id < 94 then (if id < 89 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))) else (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))))) else (if id < 99 then (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)))) else (if id < 102 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))))) else (if id < 115 then (if id < 110 then (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)))) else (if id < 112 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))))) else (if id < 120 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))) else (if id < 123 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))))))) else (if id < 147 then (if id < 136 then (if id < 131 then (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))))) else (if id < 141 then (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)))) else (if id < 144 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))))) else (if id < 157 then (if id < 152 then (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)))) else (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))))) else (if id < 162 then (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)))) else (if id < 165 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 2, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 112 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22912)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 58 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22913)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 5, 6, 0], ![1, 2, 3, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 6 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22914)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 5, 6, 0], ![3, 1, 2, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 75 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22915)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 1, 5, 2, 6, 0], ![3, 1, 2, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 128 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22916)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 1, 2, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 98 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22917)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 1, 2, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 161 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22918)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 5, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 1, 2, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 91 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22919)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 1, 2, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![3, 1, 2, 0, 4, 5]], proof := .low6 (![63, 146, 3, 72, 96, 29, 8, 20, 40, 18, 52, 86, 21, 122, 60, 76, 99, 134, 38, 42, 81, 103, 34, 124, 119, 56, 137, 54]) }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22920)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 41 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22921)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 5, 6, 0], ![3, 2, 1, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 155 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22922)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 1, 5, 2, 6, 0], ![3, 2, 1, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 111 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22923)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 2, 1, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 110 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22924)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 120 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22925)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 46 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22926)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 153 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22927)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 163 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22928)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![3, 1, 2, 0, 4, 5]], proof := .tail 163 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22929)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 138 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22930)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 120 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22931)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 10 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22932)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 57 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22933)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 14 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22934)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 5, 1, 6, 0], ![2, 3, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 160 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22935)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 102 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22936)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 5, 3, 1, 6, 0], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 74 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22937)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![3, 1, 2, 0, 4, 5]], proof := .tail 123 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22938)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![2, 1, 3, 0, 4, 5]], proof := .low6 (![37, 90, 106, 165, 87, 29, 44, 113, 30, 116, 139, 35, 127, 78, 84, 114, 47, 143, 7, 157, 5, 78, 129, 45, 85, 22, 24, 54]) }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22939)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 120 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22940)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 142 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22941)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 1, 6, 0], ![2, 3, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 160 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22942)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 102 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22943)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 61 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22944)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 6, 2, 3, 0], ![4, 5, 6, 1, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![3, 2, 1, 0, 4, 5]], proof := .tail 55 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22945)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 6, 1, 0], ![2, 3, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 118 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22946)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 121 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22947)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 6, 1, 0], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 39 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22948)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 5, 6, 3, 1, 0], ![4, 5, 6, 2, 1, 0], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![3, 2, 1, 0, 4, 5]], proof := .tail 9 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22949)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 5, 6, 0], ![1, 2, 3, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 16 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22950)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 6, 0], ![1, 3, 2, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 27 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22951)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 112 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22952)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 3, 2, 0, 5, 4]], proof := .tail 58 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22953)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 5, 6, 0], ![1, 2, 3, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 6 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22954)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 5, 6, 0], ![3, 1, 2, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 12 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22955)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 1, 5, 2, 6, 0], ![3, 1, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 128 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22956)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 1, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 3, 2, 0, 5, 4]], proof := .tail 98 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22957)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 161 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22958)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 5, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![1, 3, 2, 0, 5, 4]], proof := .tail 91 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22959)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![3, 1, 2, 0, 5, 4]], proof := .low6 (![63, 146, 3, 72, 148, 151, 145, 125, 159, 68, 149, 32, 19, 122, 60, 36, 32, 134, 25, 62, 32, 103, 126, 32, 141, 133, 88, 32]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22960)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 115 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22961)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 4 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22962)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 1, 5, 2, 6, 0], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 111 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22963)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 3, 2, 0, 5, 4]], proof := .tail 110 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22964)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 150 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22965)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 77 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22966)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 153 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22967)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![1, 3, 2, 0, 5, 4]], proof := .tail 163 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22968)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![3, 1, 2, 0, 5, 4]], proof := .tail 166 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22969)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 138 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22970)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 150 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22971)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 10 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22972)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 57 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22973)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![1, 3, 2, 0, 5, 4]], proof := .tail 14 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22974)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 5, 1, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 160 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22975)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 102 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22976)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 5, 3, 1, 6, 0], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![1, 2, 3, 0, 5, 4]], proof := .tail 74 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22977)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![3, 1, 2, 0, 5, 4]], proof := .tail 123 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22978)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![2, 1, 3, 0, 5, 4]], proof := .low6 (![130, 90, 106, 165, 148, 151, 71, 156, 30, 33, 93, 32, 83, 78, 135, 89, 32, 143, 7, 92, 32, 78, 53, 32, 31, 133, 28, 32]) }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22979)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![2, 1, 3, 0, 5, 4]], proof := .tail 104 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22980)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![2, 1, 3, 0, 5, 4]], proof := .tail 158 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22981)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 1, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 1, 3, 0, 5, 4]], proof := .tail 160 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22982)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 1, 3, 0, 5, 4]], proof := .tail 102 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22983)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 1, 3, 0, 5, 4]], proof := .tail 61 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22984)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 6, 2, 3, 0], ![4, 5, 6, 1, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![3, 2, 1, 0, 5, 4]], proof := .tail 55 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22985)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 6, 1, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 3, 1, 0, 5, 4]], proof := .tail 118 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22986)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 3, 1, 0, 5, 4]], proof := .tail 121 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22987)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 3, 1, 0, 5, 4]], proof := .tail 39 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22988)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 5, 6, 3, 1, 0], ![4, 5, 6, 2, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![3, 2, 1, 0, 5, 4]], proof := .tail 9 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22989)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 5, 6, 0], ![1, 2, 3, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 154 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22990)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 59 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22991)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 100 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22992)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 6, 0], ![1, 3, 2, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 97 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22993)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 17 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22994)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 95 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22995)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 2, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 108 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22996)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 65 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22997)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 58 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22998)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 0, 6, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 132 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22999)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 2, 0, 6, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 162 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23000)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 5, 6, 0], ![1, 2, 3, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 82 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23001)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 6, 5, 0], ![1, 2, 3, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 59 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23002)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 4, 6, 5, 0], ![1, 2, 3, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 94 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23003)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 48 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23004)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 117 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23005)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 2, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 105 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23006)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 2, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 136 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23007)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 4, 6, 5, 0], ![1, 2, 3, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 107 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23008)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 5, 6, 0], ![3, 1, 2, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 109 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23009)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 6, 5, 0], ![3, 1, 2, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 79 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23010)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![4, 1, 2, 6, 5, 0], ![3, 1, 2, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 64 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23011)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 1, 2, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 11 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23012)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 1, 5, 2, 6, 0], ![3, 1, 2, 0, 6, 5], ![1, 3, 2, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 23 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23013)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 1, 2, 0, 6, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 109 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23014)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 1, 2, 0, 6, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 2 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23015)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 1, 2, 0, 6, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 70 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23016)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![4, 1, 2, 6, 5, 0], ![3, 1, 2, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 50 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23017)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 1, 2, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 164 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23018)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 1, 2, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 1 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23019)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 1, 2, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 43 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23020)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 1, 2, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 167 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23021)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 1, 2, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 26 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23022)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 5, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 1, 2, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 91 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23023)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 6, 5, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 1, 2, 0, 6, 5], ![3, 1, 6, 2, 0, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 69 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23024)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 1, 2, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![3, 1, 2, 5, 0, 4]], proof := .tail 0 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23025)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 5, 6, 3, 0], ![1, 4, 6, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 1, 2, 0, 6, 5], ![3, 1, 6, 2, 0, 4], ![3, 1, 5, 2, 0, 4]], proof := .tail 80 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23026)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 1, 2, 0, 6, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 1, 2, 0, 4]], proof := .tail 101 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23027)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![2, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 1, 2, 0, 6, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 73 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23028)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 66 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23029)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 51 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23030)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 13 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23031)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 147 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23032)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 15 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23033)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 152 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23034)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 144 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23035)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 49 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23036)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![2, 1, 5, 3, 0, 4]], proof := .tail 140 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23037)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 1, 3, 0, 4]], proof := .tail 131 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23038)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 67 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23039)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (22912 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 22912 ≤ id.val) (hhigh : id.val < 23040) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 22912)) = true := by
  let j : Fin 128 := ⟨id.val - 22912, by omega⟩
  have hsum : 22912 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (22912 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard179
