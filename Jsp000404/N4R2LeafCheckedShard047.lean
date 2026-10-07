import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard047
open N4R2RowDataReplay

-- Original cycle 00425d1d4ca58e61748b4b161ec769eee545b3c3b13df13cdbaf0ff9875dd09e; original global index 23.
def localCycle00000 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 13 1, .gapUpper 4 3]

-- Original cycle 00b98726254c3443c354c8f819b09e131775cc56f0160f04bb7ae35440be349b; original global index 65.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 00e1d9fe4c91a6a04c8f9cd3dddf15459035f84af39d3170c3709a60e07bd8d8; original global index 75.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 4, .gapLower 0 3, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 01516a812e41d1818ed1cafae8ed82d9e696971779b097096572f0f8771d8d96; original global index 112.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 01d0ffa4b9a7d7c1f9ce1906ea8dcdba488a8e501842d4c7b9ea7bb46c575fb2; original global index 145.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 01e59d3eb00e66cfd24011aecdc52b86ee612f175a9520c3ae42cad693fe3524; original global index 153.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 01f9f028d437a6ed6702aacd85428b086fe6709d281767ea35c66a4233fb35f3; original global index 156.
def localCycle00006 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 02105e85d8b238e74558d6474d42a9065fe614ddcf2aa2826390dc4a3004e5b9; original global index 169.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 1, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0258ad2ac8c54cbf0b124f1bb7d0c035a21dddb09d4b89564cfdb9c8ea87511c; original global index 186.
def localCycle00008 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .triangle 23 1, .triangle 29 2, .gapLower 6 0]

-- Original cycle 02abec45e8353837749761c6603736dd9aa1295fa559c5bb833192381516fa8f; original global index 209.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1, .thetaLower 1]

-- Original cycle 02ac88d4855ff6e0c209e1d5d729852ccec41a876797e3f77adb5a5043f0c510; original global index 210.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 032a1e81004f63eabc24c47684354feefd786eef8109b11506396ce3e46cae1a; original global index 255.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 03458773f770bd7ddcba6676d6e503e39fe4dd140b3aa9236e4176e7cf68f6b9; original global index 262.
def localCycle00012 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 8 1, .gapUpper 2 4]

-- Original cycle 0362224bc6cb608442cf4794a2cd945fd69d310f15ac3640ea270c1540104f15; original global index 273.
def localCycle00013 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 3 6, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 1 1, .triangle 21 1, .triangle 11 0, .gapLower 0 1]

-- Original cycle 0392e1e4bca978ce5f53586037e6fc5fe7f4a030b2dfa004011085a6cfdf3ea7; original global index 287.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 03b392938e83ec85ed1c411285ec897e89a321a952a78fa35b163843bab8732b; original global index 301.
def localCycle00015 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 23 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle 047e2907fb45eb90fcba85fcfeef8cb02dbae122babee3f0c35a8acd50f22a82; original global index 356.
def localCycle00016 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 14 1, .triangle 30 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 04911b1cabb647805ad1b8d0a8ff4ca8d9dc1df024e9dac77d31de7b49f48c25; original global index 359.
def localCycle00017 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 1]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .triangle 11 1, .gapLower 0 1]

-- Original cycle 0520fa543fde4d8952794b4e2bb105ea7b9e36027c1699ee7a52d6ce9c583b4d; original global index 417.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 2, .triangle 30 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 055658e4ed14bbedba71b6d505c32bc01d1fe2c2bc80513099259b5b8b4e829c; original global index 432.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 05921e81a016e1ce5f39cc494053f41f2730253d20bc24caeb5169375da17766; original global index 461.
def localCycle00020 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .theta 0]
    constant := ![2, 0, -1, 0, -1, 0, 3, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 3]

-- Original cycle 05d5599adfc396369ac17d3bb0022b28dc3b728c7ff93117b95cf49f4f22827f; original global index 485.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 34 1, .gapLower 6 2, .triangle 8 1, .triangle 30 1, .gapLower 5 0]

-- Original cycle 05f25becb20822bc4aadd8b17606b2774e8836ebed5036cbf4e39e9a0da31652; original global index 494.
def localCycle00022 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 0615ce55007f2a96b482f24a8e690b68713e7f8126340853985e059d44d066f7; original global index 504.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 06411b1739a0dcd5c54c0596c0ee341566f2aba3138d665aea66a0c471d7f3db; original global index 516.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 2, .triangle 4 2, .gapLower 6 3, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 06cf9950f712a612160bdf709685ec32e6629f724cfab4b64efd3d21ed8468c3; original global index 561.
def localCycle00025 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 7 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 075080075a9c74a606c1e99c218a05b9408217e89815f5e097e83de9e4074324; original global index 600.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 13 1, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 07e07c900646a2bc8a3d0495af20dff46f0b701dae8bae333cd309f87a74bf48; original global index 636.
def localCycle00027 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 08973fcdaf69cab29b91038a94831759aa959792b2aaec5eb8f0a71431e8139f; original global index 682.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 08e62fafe59763e33738409620d6c456d1bfcb15c2e4877f808268cacedd342e; original global index 710.
def localCycle00029 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 23 1, .triangle 34 1, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 0946133cc2c0517b492f4471bfb7bba081e58df50902e7694eaabe2719a8a986; original global index 741.
def localCycle00030 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 30 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 0a093a9858056b5fda31c185aec4c01d4b2e4ecd0f47ab0b87219eff30ad06d1; original global index 809.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 2, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 0a1815b80555f571cec55a99d01ef283033d8e472e4159c3f01265f97aa07ca4; original global index 814.
def localCycle00032 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 0abe8886588c99962080950001a9427f6174d04c2b8b0eca155fd6b9c0ae654e; original global index 857.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 0ae76b60df46f2b3b14b5abb9a77aa224870c5f1257180fba1abfdb94edab8bb; original global index 870.
def localCycle00034 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![2, 0, -1, 0, -1, 3, 0, -1, -1, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 6 2, .triangle 13 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .triangle 1 0, .gapLower 0 0]

-- Original cycle 0b3927ae5d6d7a4b25ff954ad0acfc67e1097fe021100db2cd20dba0321de8e5; original global index 897.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 3 6, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3]
    constant := ![2, 2, 2, -1, -1, -1, -3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.gapUpper 3 2, .gapUpper 3 3, .gapUpper 3 4, .triangle 33 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00036 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0b3a2a35fea42c56034ca19059b5f8c7d6ccda563b9c8ec64738479c1c18a08d; original global index 900.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 0b46b064904f51d600f32b50191f63c7a59f110848aed5f51c2950da93e7eb65; original global index 906.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 0b4bee06879f506dbfc77bd714b0304e2fe1428bad88a65127f7563eda9fe928; original global index 907.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

-- Original cycle 0c4e07730202d618ed585fb9242d2cb16ad5ea5fd2d397fb045a0d150d7805de; original global index 973.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 0c69cfb01cf110a9c66e49a82b4a94d464cbd43128fb0868c1e01abbe5036f2f; original global index 981.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 0c6f60d9f5dec444cd4e204ba25f4695c03f266c7ed0a243aa6e57af8c3fe150; original global index 984.
def localCycle00042 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle 0d1776721e4fe0cb416e7f89dddb860c3c14bc02ec6991c089db0883d37058e2; original global index 1042.
def localCycle00043 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 23 1, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0d4efb3389a08a9fa1d63292c417333613df772dc7620dc94223335586f59563; original global index 1053.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0d5360159b74d8f4e133cbcf4751e1750fa38039f3466a76fbbdbfa813629bc9; original global index 1055.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0e1127c4c5fdf451c1b5904c9a32502b56a09c8c9c9f3ad34faeb50dff35b419; original global index 1106.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 14 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 0e307303a4a75df1c4f6b22eb7279a2f58e6a0982e9093b3a8ea29a0ec8743d6; original global index 1117.
def localCycle00047 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .gapLower 0 2]

-- Original cycle 0ebbb83295789bb4d2e6bc3cff56df8312a75bded7a88a742ca02e7777ea65fa; original global index 1165.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0ec30e11fc4eaf6f681d2b0ae854c8b69a0367b90d0cd763db4f7fa2bf7c0026; original global index 1167.
def localCycle00049 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 100685b4b1c2376a9d5b7feaf9d50e8772bf2829f56134d69ba1d0e9500dca28; original global index 1282.
def localCycle00050 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 0 3, .theta 0]
    constant := ![2, 0, -1, -1, 0, 3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 6 2, .triangle 12 0, .triangle 28 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 0 2, .corridorLower 0 3]

-- Original cycle 102d72e60289c1fc87e485f87ad93f33a60ffb8c31c7509f933fc38f3a536dda; original global index 1301.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 104276d2c4a07f932099858f4cc60f3e713ae8ca3ebfcb76cfc527fcd90d314b; original global index 1307.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 10ca86b44d54283b72adc24a4e9198dd148705de080a12b2f1f02fe046f81608; original global index 1345.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 23 0, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 1143ecf51ec381dd114ffd41188c6a260f8392a1f38d0b334099ba9d6cde4633; original global index 1371.
def localCycle00054 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 11485b42d13534ae80234fe683f6e4249ffb80d60f428f514c152feb79c4e63f; original global index 1374.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 11f9a6b29867e33137f83385531f3684e97d68f5851972c0198b61bd0ec5f8ec; original global index 1438.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 1267b8695847db2761ed9afded73cca88e352b10073e839b894c646673522910; original global index 1459.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 11 2, .gapLower 6 3, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 129e1edec5787627a29c9cff44bfbcc50cc5a7ba436a7621cbac55296005543d; original global index 1472.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 135fb7676ede887be895a00e9a101d1cf56fe456a1fa5d93cc7b12dbabfcf4f3; original global index 1526.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 1445becce1d7fa39817d72e0cf9bb4387ae5de65fbe59ab2479f4c374935b015; original global index 1600.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 149c3fc73fce5770090de64035895085f6fea9c5e7dfa9934a0f7c23ce687ba9; original global index 1635.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 6, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 13 2, .gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3]

-- Original cycle 14ff1054cb2702ca095e625aab248e7711f3d3b6ca063939a67e7ad739227dcc; original global index 1664.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 1617941c34b3f7a2912c6befdd02e3f98b6c0dfd7725c943bcfcd40c5d876be9; original global index 1746.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 2, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 1655b8ee3e28ed782bf31a6e7185f8b008584f58255dcb0f0e4ae795a0468ee8; original global index 1757.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 16a240a63c007920c486f6fee79f703fa7b226d6ee9bb47736364f65b1342651; original global index 1774.
def localCycle00065 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .gapLower 6 4, .triangle 33 1]

-- Original cycle 16f55965705fd74e75849958c6582e6209bdeab7cc5b90182f3a0a1ad930cc1a; original global index 1805.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 16fa84f6eb5a20a5903ff3b5d4cd771cd5696d845b24872440e84c7255c0ed19; original global index 1806.
def localCycle00067 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 172c5f5c7092bbee457842eaa754e9011613f296183184c73d96b6e05a7de5f1; original global index 1821.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 17ceb5e8f9c3505345745e2ac4b2ccb7042b1d8767d70f2d3ab24415f0714fc7; original global index 1860.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle 1811989a3bd584f40f4e411d03fe3bfd0f019f2e20a1d1373e6705b60086a672; original global index 1881.
def localCycle00070 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -1, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 7 2, .triangle 12 1, .triangle 13 0, .triangle 34 1, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 183a1b9b7a9e8a398993abcad1f315edd87a7ac5f690ed072f376782d69088ab; original global index 1896.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle 1874005b9ab5c9f133ed6b58d2b6a89535d4d4741074b564da795405dbdd67da; original global index 1915.
def localCycle00072 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 14 1]

-- Original cycle 199932bbaf4f819d143ab01c52a478b0989b538fef2f5880541432851ed00911; original global index 2000.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 19f5476b963d1ba75e801f0d02d7ab8c802598802d98562f9287c4b1faa00352; original global index 2026.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1a1cf0c4e9ca2ec44f0374597b64370599bb9afd47c882826669a35254f797df; original global index 2040.
def localCycle00075 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 30 0, .gapLower 2 2]

-- Original cycle 1a2c261239a2f592669a668f1e8b68369e2fd00fde3d003143ba82ea4956dc9b; original global index 2046.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 1ad671d7fd5f16506d8532115493beed44398f2cc7762b6bae8bdfbf9b5979ca; original global index 2082.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1ba67d8c2a00a1a73677e13a19de0cfde043108ab536eaa6a6202ac82d4253e9; original global index 2140.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1d033cb0dfc47aedf24f2a650ad2368a23ee8376e4bbbee100b4a0a16e3b92e5; original global index 2235.
def localCycle00079 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1d77dea58e452b2a24b672de6201ffc9f7e7566ddc099a6f55aea3250ad94433; original global index 2269.
def localCycle00080 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, 2, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 1d9672098015bcb53d08fcde07495b16767884f0bf11ba9744b1539f06d8d186; original global index 2275.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1d97b5a324182dd590055492dc01b7c6bee62e78140a118aa0e99da125e62436; original global index 2277.
def localCycle00082 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 2, .gapLower 0 4, .triangle 4 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 1dc748842ac4ff9df9aa09d5e88ffa0f01014314a8678efe774a90ac9a504b6c; original global index 2287.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 1dea50021c21eec9b742930b24fd37a058ac632b9790498db4c2d4b31280e3f2; original global index 2298.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 1e15236c6d08d5d37d84697127146063d236182e76a55c936df952b84e3921d7; original global index 2312.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .triangle 24 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 1e2f8df51bab65f4597eced0682558724ae290a9cb37b5f4139874ca66f6ff66; original global index 2322.
def localCycle00086 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false] }
  origin := ![.gapUpper 3 1, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 2 1]

-- Original cycle 1e809ad9bef5440368f16e1c854e629a54a5b3cfbc7a678906b7cd49a96d2e4b; original global index 2342.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 1f314a5341d4f5ffd81ecdb7f5e3a33a77ad7a3a341c910ee3b7b903b81c6f2b; original global index 2394.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 29 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 1fd21a1967bf86457e212fad0dba4562c6259245735e26a061d57d1434b39b75; original global index 2443.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 20634f5af1ce4b7707c5c6c67619d2e3a5bac9ee21eb8858866d7966556b909a; original global index 2485.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 208abf6f089d73e04e19f783d9aa89a3e85cd4227a0f285b91f27525fde7129d; original global index 2497.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 2174333ab4d9bafb42d362480b46027bf397f749f9f1227a5b5a74189f594c1b; original global index 2560.
def localCycle00092 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 30 1]

-- Original cycle 217a0f61d52c3f896343f31e37cb1da1a7013a700049c8156dd517450dbf7de7; original global index 2563.
def localCycle00093 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 218145a424dd3dab8496e793c0bd6950dd7b3b309f2277bc96724caa06d768ef; original global index 2566.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 222365e5f115e8c5531409624a46bccdc5f96963c4467adabf4b6588712a78ab; original global index 2614.
def localCycle00095 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 2 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .triangle 29 2, .gapLower 6 0]

-- Original cycle 22d7c1a91531b37fe663d4d5288e498e4ed3214afadd30d0e1b1abf05dea30e9; original global index 2666.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 2, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 22ec3129feb537e6d9eea9623d54d60784a69b57e3bc2b755f86ce28f7edeb80; original global index 2680.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 29 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 22fd1916b92c90b57e3885e326af79405b3049d40741dd61922ec8fec5716f88; original global index 2684.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .triangle 14 1, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2313372d7319241d59e220de4ed2da4eb80b3d06e2a9a848073adfa0973a7f85; original global index 2691.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 240ae26fe4481cede1f43d8dd52ad419c5416ce4de88231ae5eadeba3c930fd3; original global index 2759.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 24a65766f94bcedc5de7965873fc299c4bed3c9bb36f74411b86ea96d89bb883; original global index 2811.
def localCycle00101 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 13 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle 24e1e8086ea466959d2945aa01bd6c1e31b9a4a5cce711b009184058ade0462d; original global index 2828.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .gapLower 0 3, .gapLower 4 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 25064a411191cad7fedcd7df972db2417dd73830fa818964a86209aa5bcb4e19; original global index 2844.
def localCycle00103 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 2515231c586e573302b49fc86cebcd5b57574789761ea6c741dc65e21bb48f04; original global index 2850.
def localCycle00104 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, 3, 0, -2, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 25512b7d655d3d078c405dba0c63b578338f8e2e4c732f895a798440bf680d13; original global index 2868.
def localCycle00105 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 8 1, .gapUpper 2 4]

-- Original cycle 257179c229069be256a0a08ee98e1585f1e1ec3feaee8a83f65b909c2ecbcbb3; original global index 2882.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 25f0ab9f9bd88a7d57482caa8cb31fea5dc3ba8bde46ed0112b99ae547a2063e; original global index 2909.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 25f3140bdb316097799c59d0715f6d93938a4c30e279ff2e9fd256d4d7899705; original global index 2911.
def localCycle00108 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 4]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 4 2, .triangle 34 1, .gapLower 6 2, .triangle 13 1]

-- Original cycle 267f6348685f82bae0d26ccaacff33c181931cf68e64b598cfcb7ad0eb0b8bf2; original global index 2955.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .triangle 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 2691ea43d9c35d9289a4ce844cbeb5398bb3f23e06eb67629c58cb755eb1f748; original global index 2957.
def localCycle00110 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 6 4, .triangle 23 1]

-- Original cycle 26d15faef9d2aa867580f358ec9f2a3c5e84b363df23f933f1602d8f7c8885df; original global index 2973.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 30 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 27362dbd7fbc4c3edd56936d97e6ce4a7102d719e6919773fe01938e7558eca7; original global index 3000.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 282cdbc4106c39fef3e121fe4ef59b2f3f58c51827330e4c3681d206d92237a3; original global index 3072.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 0, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2852c49288ad846378e06b36f13defeae72922b98e6eca7eb5d2f2b39f9ea651; original global index 3091.
def localCycle00114 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 14 1, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 287ebcfa86ef467476633cb2a2193d4cc6a318dc2023126a9ba7e6f31ac0a3cd; original global index 3102.
def localCycle00115 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 33 1]

-- Original cycle 29451940ab5a8930e620a63e8dd7272b8118c1933a7529464e8bbf95d64dd830; original global index 3152.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, -1, -2, 3, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, -1, 0]
    strict := ![false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaNext 2]

-- Original cycle 2995478c803756017f5b4a41adf122b0a1989e2be29fa92ce384884939fa3ff3; original global index 3175.
def localCycle00117 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 29a9d9132bec99606111fe730c0badd1c79d51c779c5c7da452adc4edd99d111; original global index 3180.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 29b419966c09a13c5a7043e7cdd5589ca3fcfa7bb4a946d309c77829fbd53ae4; original global index 3182.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2a21290ea3e75026bc272a425feb073ffd1d77caeb5808a7b33bc9e72f9b55ea; original global index 3212.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2a2df5531634bf32c192caf87ce0282534362d886ba57ad17edb8f10babab5cd; original global index 3214.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 2a6a566efa8c43779c52fda59c7a2904a8b048f977cba86bd96eeaeeb3948f09; original global index 3233.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2af4aee32e28a9eed6f7d4cbedef67cd21a682203ddcb4d3188cde5724932dae; original global index 3275.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 30 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 2af7c156b8a2ba377e32d7bb8401d2aaa02db4fadd20c6e12e574999890646c8; original global index 3276.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 2c35e4f9451b7daf29fe3452b481b5ce5d611727002fb5b6df56a1e40df38eb5; original global index 3384.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 2c7c44bcfd593b1223f4b59f598f8568deefe76cb07e4cb8001ad56c5b680f7f; original global index 3398.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 2cc6bd575b36ac9199fd2a079218ac9a463a73346d167f0fbc1e2c6f45c755e8; original global index 3418.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 2da5121bb804ec8adead77bd1a485dde1f8f413971faaaadf22d6e5a24c1606e; original global index 3482.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 2da57801202d38154704a7a587a5697ea89ab22d0391ba17682d4cacb8e6406f; original global index 3483.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .gapLower 6 3, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 2dad78b0ee81cf0d8d0049a33c17146f94b8128fe26132e7e21c7b4f69554bee; original global index 3486.
def localCycle00130 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 2deb47c82a6bd25a2df10b2def1fe690a54a56524f52cccc33283b9a62ae05b1; original global index 3508.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 24 1, .gapLower 6 2, .triangle 8 1, .triangle 29 1, .gapLower 4 0]

-- Original cycle 2e468fc841f9ad8637eacb266728135d2a0aa9f07582c009ee431842dc1d7ef1; original global index 3539.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 2e7a39422b2419f63dc7a4d33ee20a5c93febadd8ccc62c885a7bbba7448f483; original global index 3553.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 2eb0df26266cca75ed23055a267c241df26970394633def318e43a595fbf46f8; original global index 3572.
def localCycle00134 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2fb229b74baac37f2175a512b209eba0cea1a6418b73df83a853a0bfbe63382c; original global index 3645.
def localCycle00135 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 3 6, .distance 5 6, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 33 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 3085a84e80a28fd5164cd4d88971b9355169bcf99cff296f27b8819ffa28429b; original global index 3693.
def localCycle00136 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 31885c9d1124f033d9d79b67ab4eaffafce3871732ec64f0b25497b15fc9be96; original global index 3777.
def localCycle00137 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 2, .gapLower 5 2, .gapLower 0 3]

-- Original cycle 3313e2d89d2b09c776d46308e80e96b845a8d9eaaa7257b0d0faa3fca6abfa92; original global index 3909.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 3376642a96131b9eeacd645104478b0d06b24e6cd9a6624bcaf042eb97c0c52d; original global index 3937.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 33c31bff0587434d00d586df344731b88697c2ff3476dc8247adcdb1f04f762e; original global index 3969.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle 340e839321fece43c7106eef6930b48ef76a146f2d29db0456624cd38abcabae; original global index 3989.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 34260fe4b4d7612e5d369c1c3f21f4ada72e2797f004a43f90c222e506b26c6f; original global index 3998.
def localCycle00142 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 34 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 34362967c3a28383fa6a6ff76ead39386835e57175c1136fe71a6058b0ce1ef7; original global index 4001.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3482594232c47b7e93ca52f96dbd8812e33c658af621433583a2a48576e27eb3; original global index 4020.
def localCycle00144 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 3494bdd3cdb29e51e48a21ec566c2f967f0bbcbe2e4f1866d4921815c1039fa8; original global index 4025.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 29 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 35aeb859721850ffa6009e4042f4c7d034cb135efc0e4bd50c4ec5517a6f93f5; original global index 4112.
def localCycle00146 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 35eaf988da26314fa1e0ef20c965da8df6787e69a40d980b03a9ab4d5c3c0080; original global index 4138.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 368df2626ca45afa1a79b8eae932b2ba95e23423dce56dea6e2b868298b9f46d; original global index 4190.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 36bc0c571b4d838f4b243a740521fcee25f09c050ce1c8e979b502a623ceabeb; original global index 4207.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 377f04ab21e77a72785adede4035872dad8d71fad3f11a625531be68601a8270; original global index 4266.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 37d26439a8a686c34c15a07903c6de58a83a1ea8074541f01bd213983f804dd2; original global index 4292.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 3870cdb442f8032b1cfe049cee7f5d95c46047318e35f98cc0c5dd6fc858e560; original global index 4342.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 38ad3493cdc310e6b42f50ee174606bbdcee0ed90ec0d769a7195604a5acc8aa; original global index 4361.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 2, .triangle 30 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 38cde308613d92ed2353c449bb71210e4ce471fadc8f3e99c4735d55115091da; original global index 4371.
def localCycle00154 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 390973a28aff14e4236c9a50af85ad4c9cb11b0df862e556f05321678e2dbff4; original global index 4387.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 3943ddeaaa72045b2642235b1e97f3040e57b7c1c4278c8015136cd52037c3ce; original global index 4405.
def localCycle00156 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .triangle 13 1, .gapLower 0 2]

-- Original cycle 395e9dcf445f350b1470179dadcdba79cb3b0fcc79b57a9dff7b7c688d3e6f14; original global index 4418.
def localCycle00157 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3ac681657c78b76958a13af6fde2ae3e5640f2a5035ed574a9e23b7948fa278b; original global index 4539.
def localCycle00158 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .gapLower 6 4, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 3ae46a676210c291a877c0739780e8ebc30d738693b95b57f9ab781d6937f9c1; original global index 4548.
def localCycle00159 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 2, .gapUpper 4 1]

-- Original cycle 3ba86a5e3ef128e450c80f359a195989a22e90b2ad087b14587c7d9b6d19c364; original global index 4613.
def localCycle00160 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .gapLower 0 3, .gapLower 0 2]

-- Original cycle 3c8fa76e1eb037596aaa547a936fa82c42a1704b4af169a0e93a1448c99396ea; original global index 4697.
def localCycle00161 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 3cb3232bef2c5e86e7cd7249056cbe2ba31d942d4adeebc702c46ab6e2081721; original global index 4709.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 3d78532c872d3cd4e9de1e8670f28e608ebff05873cfd2e5274705414a0b297a; original global index 4759.
def localCycle00163 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3dffe529cadb05ebca01693d0d8da07da572589c16f326297ad1a7207e8a8392; original global index 4797.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 3e5549d41442cffa2bfa4239b0e0cb442c481fc7daa3368295a4610b7d7dc001; original global index 4825.
def localCycle00165 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 2 5, .theta 2]
    constant := ![3, 0, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 2, .gapLower 0 4, .gapLower 5 1, .corridorLower 2 5]

-- Original cycle 3fc63d7ba51a08a684f92211372d150ab5028fbf9891eb1f76f306025a8f1396; original global index 4926.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 405bea06377b439baa1d1c78ea729f42577939984f1570448af74b2c2a7ab0fe; original global index 4974.
def localCycle00167 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1]

-- Original cycle 405e5d0ff732911419f47f03210bb6b792eef26589660ca0fc5be597fb1f109d; original global index 4976.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 2, .triangle 3 2, .triangle 14 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 4097ea5ef57fc87af0e464a01eaa1e928b53fc89aa8f4109435db19653713664; original global index 4993.
def localCycle00169 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4255e3b4170df368fe784dda4e849595c10d0d09f957484a04f49307e794ba00; original global index 5109.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 42c2227ea2d6b4538663863bff1066c8557666f3131d7f7776c5da94afd86f88; original global index 5141.
def localCycle00171 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 42e83c3e0bc8459a5f9ae6ac1cdaa677cb2d9cfe6462d8bd128113e0a2b0a398; original global index 5152.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 6, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 2, .gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3]

-- Original cycle 42f84bb9404033f608e2312e7b891177af33c7da31e676c4656a0b7483b42c76; original global index 5166.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 434622a4c3dc5257a7abeb6138c8c233790520801cebd5ec03a0ae9aab7cae5f; original global index 5191.
def localCycle00174 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 6, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 14 2, .gapLower 0 3, .gapLower 4 1, .corridorLower 2 4]

-- Original cycle 4456ee5e08c14b1bc941ad5357b891bba9f08d9f740fbed321f072c74f98cbbe; original global index 5291.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 44865acf1630f3ba36b48f579279b19ca6b9e675c2d57f2a1f885c35a257dcfb; original global index 5302.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 4490b7ca9fc92edf799f8f6fb920a1b62893747deb35e854ff23ccba46043d01; original global index 5308.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 452a47ad1eaed52a29541673c9edd208a3a137a7ea83002d4d835e7f1df390ac; original global index 5350.
def localCycle00178 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 454fc8c4e035f792c12ab714467d1e9c02f3a3e3fb0e968ad6b43f4e036a385d; original global index 5363.
def localCycle00179 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 45f1a5552ac69a7df9a06ea30cb92391f0dba700f0b5988b8747d054e6d56acf; original global index 5410.
def localCycle00180 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 46f8b5ed1cf91e01381f195892786878ddc1886a0297632f57f89531c6bb5a06; original global index 5499.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 482c10f346f8e45163a9f2bed221af2f6ef9513f04b4377fd836ecf5f29afa3a; original global index 5589.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 1, .triangle 23 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 495d71c0ad285f12f9372117d26cc3106a9fb976a5256927b77ffdf7d25d7e69; original global index 5686.
def localCycle00183 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 49b19c9b3d939d58c2b4c8828e827770cd3def2c1e27ba2bd52858dd349d2434; original global index 5717.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 4a373a4c2889d846287b363f8f6f788ccce42dbafd8d13da1085dc773591f051; original global index 5754.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4a7cc3bc807662c612aa42a2c33eb252d45a3bf4e3f62e268ceda4ca12df1e2b; original global index 5775.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4bb0c156d160ce65218afbc6702422cea786c641686ecc89c9bb13194ed6d1e6; original global index 5876.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .triangle 29 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4c4746e5e1386a772dbd81d0913033d74b4e91c64c2e380690a049c4a3d9e613; original global index 5919.
def localCycle00188 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 23 1, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4cf0c6b28d77e248570e2372f100bd8098d8fb4d3d8154cc9d23c89137d48aa9; original global index 5975.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4d25e0b18e9deaf4870bc650502f6f55c16997ded0b7ab8dcf7b729e4feb5c7a; original global index 5989.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![4, -2, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 8 1, .triangle 29 1, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 4d3a4725fb4aa614dba302a529ac9a87c654e25be8d644c89ff65b74827df115; original global index 5998.
def localCycle00191 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 4d72eaf9510a51e32cd6a0243718a6465b3b29a1d1bfcf18a7bcf041b696f74b; original global index 6012.
def localCycle00192 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4d83e9fd12b5e3185769b51b96e3ee4fc92a6496af287ce74e452415bce3ca20; original global index 6017.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 4, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 4e3349255de6469e9c88233e3b6524d9d1931939928bb41fb70299ec43308656; original global index 6071.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 4f2f06acd386c30cca791b6fe38b18b6762a0d00b2fda47f4afb0b6c974252a1; original global index 6154.
def localCycle00195 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4f5b875a1284a609c3f4a3b8b555f849c49838b343d3a38cef56adc625199839; original global index 6168.
def localCycle00196 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .triangle 13 1]

-- Original cycle 4f61788331c4f6db349e64c340fc42364cb410ad47dde21bd400bb69ae551231; original global index 6170.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 4fb34eeadd552adc589fa7675091b65d6364260d629e51a6d347cd5708332068; original global index 6189.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00199 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 50219da1b7595e5ac9618bf94af4aa9dca43b4daa9e8d1b4f504b4ed15ce73db; original global index 6218.
def localCycle00200 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 5, .distance 0 2]
    constant := ![0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 6 2, .gapLower 0 4, .gapLower 5 3, .triangle 28 2, .gapUpper 2 4]

-- Original cycle 5028c962bf145008a32d1d76f4257ee3d3f7640b5147cd3064381e8287380141; original global index 6219.
def localCycle00201 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 4, .distance 0 6, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 6 2, .triangle 13 2, .gapLower 0 3, .gapLower 5 2, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 509fd1ca242424ed6315ffb0f7afc418312a74ad9ec40dc39261a83679647337; original global index 6257.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 50e01696d6556be7211e8922bf35d71b63280ba1cf5e4cc595a2c1dd400a722c; original global index 6280.
def localCycle00203 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 510edb5ed5db97fc9f9651a1745266be1e834ca4c5296e850d63c02f71a87755; original global index 6294.
def localCycle00204 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 5117c7a911969e7515332d06b9a331a12be2cae1e1aa427ede65e0f6f59d337c; original global index 6296.
def localCycle00205 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 512154935926d5d99eec38d5e00f16ec1df3d426d7a57e8cf75b354b3d3fb815; original global index 6300.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 24 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 5174f03a6d8ef61fd472a4d89ee7e6bc227046b938d606ca7f32d8afa81d92bb; original global index 6334.
def localCycle00207 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 21 2, .triangle 4 2, .gapLower 6 2, .triangle 29 2, .gapLower 6 0]

-- Original cycle 51ee76393fcad12c7095724ed091de371de7b305f81279d2e6db6df420e8853f; original global index 6372.
def localCycle00208 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 3, .triangle 9 1, .gapLower 0 1]

-- Original cycle 52030f41d06fcd5a4e6162ac20bc5759beeea1ab74aa69caa779f612f11afd65; original global index 6379.
def localCycle00209 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 520e47a333efef32b54d62c0b711e9085d305efab20d5c26023f0828844309a7; original global index 6382.
def localCycle00210 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 523040b87d6492ec491468f9918044d40cfd48cd3fa4ac058c4096f56227aed8; original global index 6389.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 52744ae2bdec6e46de468c9b674f455eaca06350578308d4b2cea37e3d2c610d; original global index 6411.
def localCycle00212 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 3 2, .triangle 7 1, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 53ee25a2768762f8c21e0b9f049110b912f64f3dd77ee96131c584ffde22ba36; original global index 6511.
def localCycle00213 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .gapLower 0 3, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 553e34b80fa6cfc0f755944c7d1ed113654d2c963e59c708a8bf67d828f91c3c; original global index 6599.
def localCycle00214 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 2, .gapUpper 4 3]

-- Original cycle 55c370208f93f7c12558090e13f4c8a82fb782a5f06a0d25ca9287843acfbff6; original global index 6651.
def localCycle00215 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 6 3, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 56ea0e728f16a0087ce144f00e1bac8456819ed30517b476ef2c8419cd57cac4; original global index 6742.
def localCycle00216 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 570b50aac6412f5d422b151d08d4b3aad6d2aaae6e4be4f8eb68b8aea5ea9abe; original global index 6749.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 576736137b810ed39255801958b810eaa0564236f263cbb6ab5850916923b6ae; original global index 6778.
def localCycle00218 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .gapLower 6 2, .gapLower 6 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 576ee78d3c8c809fd6eca08c154434bdbd10168d871b4bceb8888e98056c0ac3; original global index 6782.
def localCycle00219 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 23 0, .triangle 29 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 578338889670ec6dc70b3083daabfad95c09825920409422929959273cb5d117; original global index 6792.
def localCycle00220 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 581a80d99d839b9f66ff25d08e531a60be0668f5fd5819aadb0b6431c8212494; original global index 6836.
def localCycle00221 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 583a30ac18b97b6cae31d9fb301a3ea42ce163fa0c75444ba44a429496f3f35c; original global index 6845.
def localCycle00222 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 13 1, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 591102f3f67aaaba4da1d31e03e0b07fe27f6de693b625c3fdd4ae55f1f02ab7; original global index 6906.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 592f5a509bb49aeb899a84afa94f87d6debd17e4925070a3f6361ab517c22fc9; original global index 6918.
def localCycle00224 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .corridorLower 4 6]

-- Original cycle 59709616f54c0efb615df770399e266e147f7567c19ca61cb7584b5593ac21b1; original global index 6946.
def localCycle00225 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 0, .triangle 14 2, .gapLower 6 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 598f663aae560e09290b18a3ce322562f8b18eef84a9859329f818c8d36bc945; original global index 6962.
def localCycle00226 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 59b2967264f901cc1d6f865b132f82919ffc7c7efd2df32f9f105a35a54974b5; original global index 6979.
def localCycle00227 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 30 1]

-- Original cycle 59e0d6317bdb989a12683a1e7fde4aa0d830fed07c7d643559a4e9dfa3c9fa1a; original global index 6991.
def localCycle00228 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 59f827e1c03460bb525df4634c8201a558314f6d9d5f6e802a54442156779493; original global index 7005.
def localCycle00229 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 2, .gapUpper 4 1]

-- Original cycle 5a62c2d8a4e119c7b10b109e9d58623b2a711d54dea7eb494ec66e2e6b83b267; original global index 7034.
def localCycle00230 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 29 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 5adb98f2cc19d6bd6ef793e56314ebc8e9b4e9dfdb0b4de6b17b60df41d3d64d; original global index 7076.
def localCycle00231 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 5b1834896617a83f6cb2f1d1f0859abc4ec7bfd3ee0344279a858d6eb143f214; original global index 7089.
def localCycle00232 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5b22d7d17d4c36c9a0b9c7088e9fdbecb5958fa1906fffa6d27063d0a15b9b5f; original global index 7093.
def localCycle00233 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 5b2ac214a60d3e628b8735f4f92b738e1e0eeeff47ef4eba4785fec48f945b36; original global index 7097.
def localCycle00234 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5b3b4f780b47a04bdbdf08d3ba817566a6cf468a3f0d33f27dcd8c1ac1e37de4; original global index 7101.
def localCycle00235 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5bd1e7016dc8d4b6492f0bcbe60ee3c9d968dd1203c088d4e73b28519cbd8cd2; original global index 7138.
def localCycle00236 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 3, .triangle 30 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 5bf3b1f369561a1d3b6f3dd9c5f925b792e073ae9c2ff385141d4143c2512a87; original global index 7152.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .triangle 34 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 5bf7957264ad171cedd8863f475de1f52adeb2f08371151f623b8a4d5cf0809d; original global index 7155.
def localCycle00238 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle 5c3ecec023570ace9d4fcd7651d844cef3148c3450d8dbe99a0ceda6460f1154; original global index 7182.
def localCycle00239 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 14 1]

-- Original cycle 5d74c7e23146a282819ef054e3cbdde7a0dc89d4811c999e233b208137d556e6; original global index 7276.
def localCycle00240 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 3 2, .triangle 14 0, .gapLower 6 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5d8904f00da58b11e119d694f785d94d10b3566923183cf603b8c233215b1273; original global index 7280.
def localCycle00241 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![4, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 2, .triangle 21 2, .gapLower 6 4, .triangle 13 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle 5dd326e50296b8afc817b03d135a81f9187ae8bd8004249f939c283978b1656d; original global index 7297.
def localCycle00242 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5e3c01745aa3dcb18e7f89737e366787341a049a17d01f5780e582bdd13d3171; original global index 7328.
def localCycle00243 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle 5e3e802513428a8e5dca1236467a7012383f694c9f3d7e7a246a7e56c4e9afd1; original global index 7330.
def localCycle00244 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 5e9f6d8560b059b5c7a525e18a923a0084a514ca995e33e28762551fd419665d; original global index 7361.
def localCycle00245 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .theta 0]
    constant := ![2, -2, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .corridorLower 0 6]

-- Original cycle 5f4d055f418911d5ef011681d6a4407009d3d66fd53b1db19f2a1d2c44f15fda; original global index 7419.
def localCycle00246 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 8 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 5f57a43b550d4e658c63f25de3fc411fa1de98a5b94850f6f08c2cfbc01ebf04; original global index 7423.
def localCycle00247 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 8 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 5fee8eaea7bc333d920db0e404a561a0197bdf3e791d1151b2be764c1ad2f6d2; original global index 7480.
def localCycle00248 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 31 1, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 602979727d86877479ac42307777f06b789d27aeac2fcb09d20e70cd1963406c; original global index 7492.
def localCycle00249 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 14 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 60778c7929f37139bbc9b97d9bf26a79eee57c7d3a12aacf334bc16a7af221f9; original global index 7512.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 24 1, .triangle 20 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 609cb687f53a157afe1f858b91f42d8676b645c5c6d578988cf5fcebbcfe0235; original global index 7522.
def localCycle00251 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 616513a0de667fe838569324ecc18312aaf37e4f69629e07dc967bd00f6d8d4c; original global index 7596.
def localCycle00252 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 61cf2aad60066130d311e5599cb05d6afe19f7594c6ffd4f018b4117c259a3bb; original global index 7633.
def localCycle00253 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 0 2]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 7 1, .gapUpper 2 4]

-- Original cycle 62b494a19ad9e530101737b613ee0711fcc2c6c3cb820de575f5f5db67c8fb2d; original global index 7704.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 24 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6432ab7578618095d31326b44ea6dec237586338aa3cfd28aa1e479336212af5; original global index 7807.
def localCycle00255 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 22 0, .triangle 23 0, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 648539e04a06880c1c8437056efdac5cfee45658641db04535f4be1a003cf6b2; original global index 7833.
def localCycle00256 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 4, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 64a6d26c4ed5cae860db855f5958794e12264e6db394d97d18e69388167b24db; original global index 7842.
def localCycle00257 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 34 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 6573f07a59cd785af41bb1bf1342673453de163aa6df1e8741e3099efd31a5b0; original global index 7893.
def localCycle00258 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 659ad0816144278d5cfa7bc0c6991c733cf5630edd4eaf200a6a71e194aba020; original global index 7905.
def localCycle00259 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 65fea67d01f7780b3403e22f83ae1d7e7cd59321473f2f059475b00834b24c70; original global index 7937.
def localCycle00260 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .gapUpper 2 4]

-- Original cycle 6633dc2eae4ee3ad3dd2505adeb8241621238b1094b978717ec9fdb115339158; original global index 7949.
def localCycle00261 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 666677753d002b21ae365f65376a6f3f7be5760a763ed9690364ec6e5f883951; original global index 7964.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 667dc8aae7b5cdc7fa6a0c04bf15bbeafa9163e8df5a1ed575b1d34a790a1d98; original global index 7969.
def localCycle00263 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 13 0, .triangle 29 2, .gapUpper 2 4]

-- Original cycle 66b60b1820266d6a67d2cb762d086539a625f21846d5f247f46fd6aa192840c7; original global index 7984.
def localCycle00264 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 2, .gapUpper 4 3]

-- Original cycle 6759f49a2173b5d27ad98c4e21062afc46fd02a8314fbeb9f6dbf7907439a166; original global index 8035.
def localCycle00265 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 23 1, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 6794b918c5f4ed0ec5aa9e7b078142494247fbdf2e67b87539f4f99b00d5fe23; original global index 8047.
def localCycle00266 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 4 3, .gapLower 5 2, .gapUpper 2 4]

-- Original cycle 67bb5a8d723177d9e6032531ff876a9f95acd27ca4d8c96d3728ac982f37eaf4; original global index 8056.
def localCycle00267 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6803d58819d85b58fe24110607ab143a2c939c486df85a744d1214c87e13cc96; original global index 8085.
def localCycle00268 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 2, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 683af99b33e4538f17ba65535cca58bd6a4db0272e7920f6fcd6574c09df140a; original global index 8105.
def localCycle00269 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 68b251d9c6ef9cf42e28ba6dafa16eba1e039e9bc96da933623e31d87342b020; original global index 8144.
def localCycle00270 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 69026518168ecda95f8e6375a9c33d9e438f75c28e2541dc0d12b42812a48c01; original global index 8167.
def localCycle00271 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 693626bd5fab574e56abaef9052052fa8ecb7bbf1921b69a5fac4bee75f6cbd1; original global index 8183.
def localCycle00272 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .triangle 4 2, .gapLower 6 3, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 69738b8c6bb12ea758f5828e05d9f393ca316944f5290f03ad496950376b6f89; original global index 8202.
def localCycle00273 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 6977c7041aaaa5a62c7287ca16116761cc18f05276673973d522bacbd16a6222; original global index 8203.
def localCycle00274 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 69c892f6a37fb7285d39d018a7ae83913a41cd3fe2e7594e70ab8897e826dc87; original global index 8236.
def localCycle00275 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, -1, 0, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 19 2, .triangle 23 0, .gapLower 6 3, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 69f75366af3c4e91ad5e70da097939638481cbb4af703ba5a62daef4ee7dad6f; original global index 8247.
def localCycle00276 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6a2ddc240bfe0841dabdb8c56fe05cd8f689eac0242eb3a996892b254d7c08f1; original global index 8260.
def localCycle00277 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 29 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 6a532aea5e89ccf4e68e66732a2e5177e3c5f6ef96ebcc9427215014be36c6b1; original global index 8279.
def localCycle00278 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, -1, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 6a8764468a1065166d02e3aa55d140bb3ad0b057126702dbe3fcdcd9ee2d51a6; original global index 8294.
def localCycle00279 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 34 1, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 6ad8e7a8bf66ad5f277c9f384ff6b47578d1b3ae364a749c8397212dc1ff9ae0; original global index 8318.
def localCycle00280 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 6be8062d8d8ec925954f785d14af863dcb9bee248a1a63bde5eaf14bdea59005; original global index 8408.
def localCycle00281 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6c24a6f007737f051b8e11f9ede96569b04f052073b3dc7644dc82c49717f831; original global index 8427.
def localCycle00282 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 6c52e8b35653e2608f7c5a7067ea69774d1f2198d445956673f994666b89604c; original global index 8439.
def localCycle00283 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6cdc0ed03e6c19fa83854ea1c1a9939e00b62a78271c0750e02b24d779b9e65d; original global index 8470.
def localCycle00284 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 28 1, .corridorLower 2 4]

-- Original cycle 6d2585c3e5d68ffa5b35a63d9397914ae235967085bb3e223630d98d121670b6; original global index 8488.
def localCycle00285 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 13 1, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 6daf482b5379b0bb4188d57a86507bf2328dc460771a39fed17248e1eafa801f; original global index 8526.
def localCycle00286 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 6e82ddcc1b344469d71df4f536cd8b4617fd829df31bf4e6530ade8f269238f6; original global index 8576.
def localCycle00287 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6e83e1109f8d0a01e556778d8d7f1a409448e5c1fea4fa1a8ed95afc78b1f254; original global index 8577.
def localCycle00288 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6ea15ba5215fb74fde186cce4f125dd294e1c5956d981294206305bf6e022d1f; original global index 8583.
def localCycle00289 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .triangle 29 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6f65b4e59fdef7ae096399227fb6b3499935fec206b2305a2e2452d11dae75d5; original global index 8634.
def localCycle00290 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 6f980f4fb500cdcbaa7d28a4eca6ae188c477895ac3cda29f640776c4a9174c7; original global index 8655.
def localCycle00291 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 23 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 6fbec410d411fd91b1c0986d1dffb5addcf770bb8cf39210063568220142494d; original global index 8669.
def localCycle00292 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 29 1]

-- Original cycle 701018385ce293b99992b1371a1d0adb3e163c733ee45ce8a485c9f7f94a66ab; original global index 8686.
def localCycle00293 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .gapLower 5 1, .triangle 26 1, .corridorLower 2 3]

-- Original cycle 7038d077fbae03b44db0a9443a3c5d772032e05d5a901121538aa615c792b799; original global index 8691.
def localCycle00294 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 7054cb3f0417e17d8ae1f4c0332c458c72f607e2a8660cb010caab02b41f5611; original global index 8702.
def localCycle00295 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .triangle 14 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 706a78561c77e2530760241767e04b85a4464fcf0b33cbd46eea99e0b6387ef2; original global index 8708.
def localCycle00296 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 2, .gapLower 6 1, .triangle 29 1, .gapLower 4 0]

-- Original cycle 70892d998a57afcf44f536326afc494db82e1d375bb3762b6f192fe773451bb2; original global index 8719.
def localCycle00297 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 24 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 71231ce1bd37d063ad84be33778037cc0888f64dbcc2fb58f91a589d22a2dc94; original global index 8776.
def localCycle00298 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 2, .gapLower 0 3, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 71fab347a3fc45ae3903caa75065e95f6a4c4005751aa29afaa5167a577747c3; original global index 8833.
def localCycle00299 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7249dbbe0ccdc40105b5701998b4fdfa84ac08e2489009b5202e3ae4c2f30883; original global index 8863.
def localCycle00300 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 72bb7091187f7e4b8c3f18dbbf2826e5ef6b69f05d830b49e3bfcfa3e5276cdf; original global index 8883.
def localCycle00301 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 12 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 73240cabf017ab8c45a5741ca2eb5779562d270a62723609ea27efb5245ef7c2; original global index 8916.
def localCycle00302 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 735d3b737f024503cd4a428f9888f2a0fd732c42a2db0a122c981866a29847b1; original global index 8936.
def localCycle00303 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 1, .corridorLower 2 6, .thetaNext 1, .thetaLower 1]

-- Original cycle 738b868defd7b296aea4b42e857713d754e7aff66f80345ddbd50e268adb9500; original global index 8958.
def localCycle00304 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 7408dad13d7ebff7119c8bad89859cb49ca0e8adbd125c674f166658f2872dfe; original global index 9003.
def localCycle00305 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 3, .gapUpper 4 2]

-- Original cycle 74428463e9621c620d208c988029fcf0560c63093a7f44577e0488efc498ef7e; original global index 9018.
def localCycle00306 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 5 3, .gapUpper 4 3]

-- Original cycle 7501a9183cfc87aaf81feb6a9ad72c8b885181e45e558909cbe00fbe9fe55896; original global index 9067.
def localCycle00307 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 75081e737a70b932f1cec7de22a6a2a567c8405203897b77c170765e1c17a822; original global index 9070.
def localCycle00308 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 7510fe574afd7e40fd3e0e231cd174148a29ce807a2afc8f8d2a42c47144a9ad; original global index 9071.
def localCycle00309 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 757aabc01cc529b37e6bc3b41efe7fa1bfb651442b636b9d391fa9d1b7580004; original global index 9103.
def localCycle00310 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 3 2, .triangle 14 0, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 76b116c9cf6de1f571240474cb098954aedb436a1f0ca5f528f56fe4fd5bdf69; original global index 9187.
def localCycle00311 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 76f1928b3cd40d9e4d06dc93842e9edd88218e9f691a78eea3b80a3787ab2103; original global index 9205.
def localCycle00312 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 78814306d1797c409605119bdfc3a05d93b2d8fa81a389b1403370966e4bbab6; original global index 9323.
def localCycle00313 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 794dd8d15376ab5110ab4cf9b637d0a23c043dcbf79ba48a4d9e92cc5f8fd457; original global index 9385.
def localCycle00314 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 798d139270cf92650e3790f2198c818eaef52d512a67545c77172ba2545ff64b; original global index 9403.
def localCycle00315 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 6 2, .gapLower 0 4, .gapLower 5 3, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 7a520217617237047c6bbcacd7c9a51abc75b247efff2c32e30c3ca17462788a; original global index 9461.
def localCycle00316 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7a926650cc56770c6f2e577c1cfeb7980f148822c53cd18a3d5bb1763d869a7c; original global index 9485.
def localCycle00317 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 6 2, .triangle 12 2, .gapLower 0 3, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 7a93f3213838d493a8ec931bbdf2660e9f31605e938eb0eb88f57baed9aaab8c; original global index 9487.
def localCycle00318 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 7b091117f0a2f15b770a0bd87ce68c36c7964bab020c6a79cc43f8f73f041390; original global index 9528.
def localCycle00319 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 24 1]

-- Original cycle 7b7faf316ac15257e0bc1520a192b509eb09e463307e743db4003400c6901d4f; original global index 9557.
def localCycle00320 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7cc5b77f7a37f9df1e0c248c48adda039326a8fc96cd6876375bd33cd98fb286; original global index 9665.
def localCycle00321 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7d0c52cf2343298d8e29458ef663ae183772088315b673c36edf81bfa0e28a78; original global index 9680.
def localCycle00322 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle 7d0fa245cdc91669b05a2b375adaa87e41b2f1c2e29278afa6229db30b4ecaa7; original global index 9683.
def localCycle00323 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 22 0, .triangle 23 0, .gapLower 6 3, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 7d2152af9fa60d88058ef6c2b992608f56cb08a491ab002722fa573d1aec184e; original global index 9695.
def localCycle00324 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 14 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 7d22db68d4eb61af2102f376610752a16ef6cb981e9b7fdf5af372528b215398; original global index 9696.
def localCycle00325 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 7d2613207b94bc2d5bb11cfa010c20600bb09c34afc18453d2862045a9d7cbc3; original global index 9698.
def localCycle00326 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 7d78f391f79b6ad01442b844b3f2feb782d02b25da15dfd8a0b003f611d3e993; original global index 9732.
def localCycle00327 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 21 1]

-- Original cycle 7df2c0229aac2bb757f95457bc98782c8c2062b7ce3207f5f5f78b555146a31b; original global index 9781.
def localCycle00328 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle 7f8716857f106c41da82f7862418de8cae9fa8d1cba1a3fae97175ad48616ae0; original global index 9889.
def localCycle00329 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 7fb775c1dfc16d7488f04a6c43214ca8741997285945cd99dd8f7ee4609c8bf6; original global index 9904.
def localCycle00330 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 807df3b7fba38a38240c05af130a718f31444048fca8e26c3fd91b8dcf1eb98b; original global index 9972.
def localCycle00331 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 14 1, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 81250c89b8c4acd3ff367b7bba062584dc0de1db6e0449d057ad9069cd8c070f; original global index 10023.
def localCycle00332 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 29 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 824b0ac2e2f4e76a3be853ca1d1a8b44439e776a945fe6475647c6c767713a72; original global index 10117.
def localCycle00333 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 11 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 825d6882dfc34871866540197c995c06d9aa87b007dbd343799a7ce4b37c7878; original global index 10120.
def localCycle00334 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 24 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 82e930ad0ddbdafad5795b8222d8b40f86cce72d4fc48c38113e64b79312a0be; original global index 10153.
def localCycle00335 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 835a2edf232aa253a840056d5d871a3e99293ba238217a204977da63a628b0e9; original global index 10187.
def localCycle00336 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 836f7ec632e94ad29194bee32b5d59d2e6112e726f11e4bf91fe1f5c0f40c5e4; original global index 10198.
def localCycle00337 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 8371ac9802f2c8da0747b60fc1e6d0b95feeed9a2d614ad62aa72426e0256b92; original global index 10199.
def localCycle00338 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .gapLower 5 3, .gapLower 0 4, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 838da4eeb0fa638a3844c7a80b73c5e73162e1be156e0d330d4a639ebcbbe491; original global index 10211.
def localCycle00339 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 2 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, 3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 7 1, .triangle 30 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .corridorLower 0 4]

-- Original cycle 846c9cf5033963ca6cf0adde8a4101c0a85813411dd19ec4db9fd9e2ccfcc9ee; original global index 10284.
def localCycle00340 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 85ade4878085463e241b0b14d326fc2c4f975884f41d1486fa023cab9987514e; original global index 10374.
def localCycle00341 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 860ac4e9c4aea535700d49ddc9d428a2f13caeaadf28e3fffa097503ced201cb; original global index 10397.
def localCycle00342 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 26 1, .corridorLower 2 3]

-- Original cycle 86c5a23f8f9c44b99b1a9f5c1d066cadd265f16d9371ff63680b5cbff3b8d882; original global index 10451.
def localCycle00343 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 875f50c69899ac34074b149a0af95cff5fdfc196543e224fc82e430a40892109; original global index 10500.
def localCycle00344 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 23 1, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 87729843a08619fc416c4c16d5da5973094422c2983e1779a2ef0e2ce6b942e3; original global index 10505.
def localCycle00345 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 878dff4cf4c363624ab24ca6c6843e16fb93c5dc2c0bd6560e838172b3f4d394; original global index 10510.
def localCycle00346 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 87ad0bfc52a24cbd4e8dda51f1bc63f3e8b276cad75b30022bf88ea688346026; original global index 10518.
def localCycle00347 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 887e23da0bdd50f824b9bd7fa5de1eebe88273fb5c260f3f74d3cf6d0e0c8ba9; original global index 10576.
def localCycle00348 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 88842c9ffdfc6487802493a94d209cb04e99b1c2242b88ec1fbf69d5caecd1cd; original global index 10577.
def localCycle00349 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 888a1a635ac8c853131ddb2755839185a27e81c3e9203beccce6fe8ddf9ad085; original global index 10579.
def localCycle00350 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 88d093fac692905103876df9787e3737957281370bfef62832f8cd2f6aa92e4d; original global index 10598.
def localCycle00351 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 3, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 8986c00239cf6fbfd68765a24e4c274bfb14f3754df869a2cdd3393dc26fbe3d; original global index 10649.
def localCycle00352 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 899d3c12c260e452f09b46dc1c3d5e5ea8b0f775e67039a63e87e81784ced8ee; original global index 10660.
def localCycle00353 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 899e0ac3c53b4223e6cb4a5a276933b09cb6d9710c8b80a4119095e4db001216; original global index 10661.
def localCycle00354 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 89deafbc0c4dd2d3ca7ea3bc6d0c1a5cf566ace0250c65a638965a4eae59c24d; original global index 10681.
def localCycle00355 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .gapLower 1 3, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 89e2aa475052d082b791e90f0ab4ef67e65b733c896cdbc01fd218cb08e0d2e7; original global index 10684.
def localCycle00356 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 8a2d464544aab6273f8ce982d5385fa39404d297b1ac16addad41442a5181f66; original global index 10709.
def localCycle00357 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 13 2, .gapLower 6 2, .triangle 30 1, .triangle 26 1, .corridorLower 2 3]

-- Original cycle 8a505ed99eaa37a1c0a0a1ac25c5956f79f92cfb15dd7f1e2285a5bbcdd564a7; original global index 10718.
def localCycle00358 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 8a579c2df132e1b17eff3c8e1bb1dd90197f76f5138b7638aefb7a80e7ac2267; original global index 10720.
def localCycle00359 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8a89a97a51beb062890cb94daa205184d1eb00dc59a0a10ec636bba31961b5c6; original global index 10731.
def localCycle00360 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 8b2b05719ebdcc8d2bd2a95d290369cfb0d424e629fad729d6e0c6f4cea1c3dd; original global index 10781.
def localCycle00361 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 21 1]

-- Original cycle 8b3d7e26bb0591d10e16447f6d9a54c5597eca9b205cf30b36c7aacfc3c13f35; original global index 10788.
def localCycle00362 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 8b43a4a162ac06c2d53d8c0c2267699b0b99fecb3d75f835f6fa95d132a39dd2; original global index 10794.
def localCycle00363 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 8bb0cc768d21bf892dec8980a8bec6ef7b4325512c7d27286a0b81d94fb6ef5a; original global index 10815.
def localCycle00364 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 4, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 8c55c578f50fc8d91a524170ea87c7339d1b35490f2bf1746245697e1df8f97f; original global index 10857.
def localCycle00365 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 8c5eb6335a0036b6fdb9fd858ac638d881144c5ec01ee6ae5a1b2b6336234778; original global index 10863.
def localCycle00366 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 2, .gapLower 0 3, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8cf848fa3a79bbbe59174d848eef64f1056275463831ac6aeed6202e9ed2ad99; original global index 10905.
def localCycle00367 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 8dba7770323103c6b60d2dbc4d3a392797a7942a8f52b142aac5b5ea608db62b; original global index 10965.
def localCycle00368 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 3 6, .distance 4 6, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 32 2, .gapLower 6 4, .gapUpper 4 5]

-- Original cycle 8df3617b77d79cebe4e9bdc3022c3ff7411fbab481efec70cbbe69a3ddc5fa5f; original global index 10989.
def localCycle00369 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .theta 0]
    constant := ![2, 0, -1, -1, 0, 3, -1, -1, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 6, .triangle 6 2, .triangle 12 0, .triangle 28 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .gapLower 0 0]

-- Original cycle 8dfa96169af82b21fab9c7f9f994bbca6f087ff3bc0f39b5a3cf0d85cd4d9b10; original global index 10993.
def localCycle00370 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8e5f9f6134fa21526e73a64baaa60d714e4ae0f9133a2645daa165d7bc8eec1b; original global index 11022.
def localCycle00371 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 11 2, .gapLower 6 3, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 9101ae8cc8264fff497beb1bd6a1a19e610680c1c2705861708139c34142e497; original global index 11230.
def localCycle00372 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 9158b40cab173c6a912c62125942324858b9f2c7f8ae88918453877b054d9ac1; original global index 11259.
def localCycle00373 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 23 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 91be7f4106e19e661e57049fb799d1e2eefa10bd3ac38d7f629a7f9dc97aa6ad; original global index 11295.
def localCycle00374 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 92c305c2e5e14a44e1968e8f959ce8ba468169a48e66523bb1bb8992369d5867; original global index 11373.
def localCycle00375 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 930bf4b019ca510eabc27643050b5c653f2ac6cd49c1708285dd74b9573292e5; original global index 11401.
def localCycle00376 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 9363c1e6ed839e50829742a60bece203be60794edbf2efc8b702c2d2b4129fc0; original global index 11431.
def localCycle00377 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 93674c84354cffe64794ad68669cc337cc332c4fd492bb65d60d84409e446c64; original global index 11433.
def localCycle00378 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 2, .gapLower 5 2, .gapLower 0 3]

-- Original cycle 938619127337ee74ad09042fb8a396268d77694b64ace1698095968b073524bd; original global index 11444.
def localCycle00379 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 3 6, .distance 5 6, .distance 3 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 33 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 93c7b6f6942ca79f3b4bb8c7fc3a8c0edc482f51d954cdff9eed8de86781b2a3; original global index 11468.
def localCycle00380 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 24 1, .triangle 30 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 93c816c8fe5cf977bf9d386613a4772daf2c303b3847e2d8d6df02e22ef38c25; original global index 11469.
def localCycle00381 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 3 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![2, 2, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.gapUpper 4 3, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 24 0, .gapLower 1 3]

-- Original cycle 940e7f1ca22483491fad8e7579a9415fb0870f95f60f66f3fb30e47bf2377ad3; original global index 11486.
def localCycle00382 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9441ca887518a921bb2ab6f7a12c356788182cc89cb259ba1cf3c1ae029ffe9b; original global index 11503.
def localCycle00383 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 949f499d382636b825ea5e3b1f99adac312948189d01b5c07f77dcfc75c9c9ff; original global index 11532.
def localCycle00384 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 94cf3e059aebbd129ed5b1fa00fe2b61501b22ad405d18e6f5d2d8516952fb11; original global index 11551.
def localCycle00385 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 23 1, .triangle 34 1, .gapLower 6 2, .triangle 8 1, .triangle 30 1, .gapLower 5 0]

-- Original cycle 94f9ebd02712cdc59061e9258edd3644c68dde79672d7fce33f9b0a0833c443f; original global index 11562.
def localCycle00386 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 1, .triangle 34 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 953e8c21043e6a5d896c9dabb8399b4b7eeb46af07fa031725fa48c84fe02edb; original global index 11594.
def localCycle00387 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .gapLower 6 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle 9546c7cb6589a77dde89354f530db26a5e05abe4b26183d3538cd5cd655cbd67; original global index 11596.
def localCycle00388 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 95d28898534bb0d357d433e19ff5499eafd2007f104c2ad25e8ade7b786ed65c; original global index 11645.
def localCycle00389 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 6, .distance 5 6, .theta 6, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaLower 6]

-- Original cycle 9605d1f7d7ae3a51b07cbf686190ba9e702e62c01c78f774c1ed1b3973e84c6a; original global index 11664.
def localCycle00390 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 967f7db8057b814c87620a8edb7801b97c3a4d7f186f3c7656d569cfd2a7c159; original global index 11703.
def localCycle00391 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 29 2, .gapLower 6 0]

-- Original cycle 96b9494473ce03ea732d28652e07e9cdb6bb9784746a6ec4403ce1778e64bb99; original global index 11720.
def localCycle00392 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9701a9bd840141edf894199b1ebd512e438d85c6baea3eb175ddbaaaa472ceb0; original global index 11736.
def localCycle00393 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 97996238a5dcff1f1a654f573608ab2291fe10122ecbddd7ddccc62cb02f4d67; original global index 11775.
def localCycle00394 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 97f66c231a34b146831a5d032eb3cc9ee2f1c9f952375a284a60422ee4ee0d9e; original global index 11801.
def localCycle00395 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 98913307323545c95c33dbb530c4d687ffd4be9f07d2787fc5f2c74d84a6d56c; original global index 11850.
def localCycle00396 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 989cc21103447b2699bb24b0c33207fb760f473be110e912e6189e292eb93f1d; original global index 11852.
def localCycle00397 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 993190166bd53d381734bb7f4219137a20a1deaf4e01819a6493b1853cd5a824; original global index 11895.
def localCycle00398 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 2 6]

-- Original cycle 994d05d5697c995fa064210c0130dba21e38b2d5f003a0e61924582d47d80845; original global index 11903.
def localCycle00399 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 9994ff1edc4a2cf94470d94b5ee838cf33e40707b9120a78a92a394fb7698f15; original global index 11924.
def localCycle00400 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![0, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 13 2, .gapLower 6 3, .triangle 34 1, .gapUpper 5 2, .triangle 12 1]

-- Original cycle 9a760333aaef13e72138293512c20bf8b4d659f7c8b3bf58a6e5f49ec6439425; original global index 12002.
def localCycle00401 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 9b0f31b8fd0de959d59b31575f650f7a9b68f6002b361be8461623e6aa927041; original global index 12054.
def localCycle00402 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, -1, 0, -2, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 23 1, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 9b362e73d3625bd626cc8d7d0ebd0b3a5d2e6da9510f1ce4c62e74a7f8a82fc6; original global index 12069.
def localCycle00403 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle 9c80c84c3c3326c3acc40e823977da357e8540e1b5c36ccf84afeca27079a132; original global index 12172.
def localCycle00404 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 2 6]

-- Original cycle 9cbd7dc368c890bf078a59d089c50f57a4413e34e3f0dfcf101873e5a2a7ea7a; original global index 12192.
def localCycle00405 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 23 0, .gapLower 1 2]

-- Original cycle 9d26a059cfd271c8cf76508db8dd986baa768f10f3f39a11bca63ac0e96cbea3; original global index 12225.
def localCycle00406 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 9dd8ec8379b88cc14a88438dc721c9c73eccdf45c087c3ffee03c0a1c947a66f; original global index 12282.
def localCycle00407 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 9dff0574e75349462395a4b4a0d8a521098643e00ea11d9b3cf07095cce4c847; original global index 12296.
def localCycle00408 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 9e143836cae4d94368dd3a9796942d9e029fe3a418b2ebc5eff801f71f5491a1; original global index 12302.
def localCycle00409 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 9e188a124fc9cf7464a89adeea8265cdaefee706751b6098977cafceb803a936; original global index 12304.
def localCycle00410 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![2, 0, -1, -3, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, true] }
  origin := ![.gapUpper 2 5, .triangle 16 2, .triangle 23 0, .gapLower 6 2, .triangle 8 1, .gapUpper 2 4]

-- Original cycle 9ebf24595abd25689c6adb80c5a9a47545faa8071b56510e99a3b1027e0d6692; original global index 12359.
def localCycle00411 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 9f5811ea2b0323d3337f4285e280c527bb8ddd21234c4611a492cca70338dce0; original global index 12403.
def localCycle00412 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 29 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9f7197df8cf397bd9302894cb0b0fe21fb36b3cae82b83f4e939a89fab46c366; original global index 12409.
def localCycle00413 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 9fb0d253640bc64108eff79a1a7a8cde0eaa4f3617c16250aa125ad1a3210ce7; original global index 12429.
def localCycle00414 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 6, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle a0de8304a76adc5df0b0f3dc985051cf1bfd4bf15c4a3e42cd84c73c174ea177; original global index 12512.
def localCycle00415 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle a21e0e14b4841faf645da1f629b10b9f25330082d5a357f1ed7979ccb9cb4a50; original global index 12613.
def localCycle00416 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle a23d967c3b65f5df8e0135023b08020cfe1ece79ba47e34acf7aa67e030a87ec; original global index 12624.
def localCycle00417 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle a34f640565dab3044ec904b6f803004cac22ae796fc1173f218ac3c632760c96; original global index 12693.
def localCycle00418 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle a3760389d43de84fac5921aa66ceaa6c8c0bc63a6a0b967060e38804962b72a8; original global index 12703.
def localCycle00419 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a41e35669cfc8e0836a1ba1e9da2275936fe01cf6ef278fd61b2887ca6910503; original global index 12757.
def localCycle00420 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 4]

-- Original cycle a4cce42e079e92e4d9065f479f6055e9f01ba77f4c7398672528dbfe0575d2c0; original global index 12808.
def localCycle00421 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a5619c57d0a0ffad0404268bc681cb8605e21acbb378c8faeac4df78cf91af17; original global index 12847.
def localCycle00422 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle a56e3826a4b2b12f245eaddcf08813b87a9bc9e0760df8bc14b1330d8468546f; original global index 12852.
def localCycle00423 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 13 0, .triangle 29 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a69cfcf9558d7add72af32d2cd29c94891621dde9a067e4a5ce2848ffebf7a52; original global index 12944.
def localCycle00424 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle a6cf7cf5c722ef63823e282c5080896785ab9aff1c04b9f4b1a9d1def25813d0; original global index 12957.
def localCycle00425 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .corridorLower 2 3]

-- Original cycle a6e2f5bf1a99cddb3a0b4916086185e1cccc215a2b587b368055017896a3c9ad; original global index 12962.
def localCycle00426 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .gapLower 6 0]

-- Original cycle a78aad184ff56937d5c937a1f27640a7bc4dd47907536d8513a3c83a0da6823d; original global index 13036.
def localCycle00427 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 4, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 6 2, .gapLower 0 4, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle a80ed325acaad30c72bd6872e27e6fdc11f753bc39b96a11214628d1c27cc0f7; original global index 13085.
def localCycle00428 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a83008e593f611acd327accd44068825f1debac42bd2e98cf16da7a7661b15b1; original global index 13096.
def localCycle00429 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -3, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 6 2, .triangle 13 0, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle a8ce667e7aa3e87a7dfe706d1945681e157402df9eceee57f7d621119dcc40d4; original global index 13138.
def localCycle00430 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .triangle 23 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle a8d8961bc6637d9d0ec1243959ad77b5952a3b54c3412db16252133bb436380f; original global index 13141.
def localCycle00431 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00432 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle aa073f98b2bf63b1a1f24771ca597b9a7f22618bd533c66658b63f34681e34fa; original global index 13235.
def localCycle00433 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle aa0b1967765188b35dda9db66712a13a579dc03b2e9d95f113c72dbee15f6063; original global index 13239.
def localCycle00434 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 29 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle aa536b7c1d1cd53107e38d3a51c0001f4c5ce8b08eaf8beb97d7a7ea7e9119f8; original global index 13263.
def localCycle00435 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle aa576dfddf12abcf9608803d03ac7459728201e2f3a3b38223ba6ef71f201fec; original global index 13264.
def localCycle00436 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle aadb77adac1196b8a1f02f634c275bc766b6d7ad439889973ba1824d3b80b579; original global index 13309.
def localCycle00437 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 24 1, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle ab3268a02c66f5010491f88ae1c22d2d552dae9318cb3bc2fbd142256c45a2a2; original global index 13336.
def localCycle00438 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 3 2, .triangle 14 2, .gapLower 6 3, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle abbb80c9dd32e34cdf45fe5e4440b08a2ee5cbd70d0bb27fd0f222bdf75131b8; original global index 13371.
def localCycle00439 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 0 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 12 0, .triangle 28 2, .gapUpper 2 4]

-- Original cycle abf02bf45f656f49b6ac1f14af01181ca002e9ddb4d18fa30e490705afcb7509; original global index 13392.
def localCycle00440 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 3 6, .distance 4 6, .distance 3 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 32 2, .gapLower 6 4, .gapUpper 4 5]

-- Original cycle abf8cde7fe43d406d63161e4f61b3498fc623df5fedbd551eb3f8592ec152cbc; original global index 13397.
def localCycle00441 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle ad0cfa8abee62ab6559434fa2e77dc6e6497888f76ffd5ea46160dba22ccc91d; original global index 13491.
def localCycle00442 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle ae0136f81edb25f8289117fb963fd3d8a51ba4968692cb8c45597f8cd086f494; original global index 13577.
def localCycle00443 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 6, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .gapLower 5 3, .gapLower 0 4, .gapLower 0 3, .gapLower 4 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle ae280161e98337e259a096539c0fef351f61fdff477175c5dd569ce008d15d5e; original global index 13590.
def localCycle00444 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 4 5, .distance 4 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 34 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle ae733903d8601094c91de934965094c52e3cb75430a457c060b3a089dbcbc5fa; original global index 13616.
def localCycle00445 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle af0e88f2f3f140a7f7283f551f95aff4915e9b8dedf9e5e6b0e1313247642a70; original global index 13668.
def localCycle00446 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 23 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle af3cbc0fe95ec9d654cb37c4ff07dba385da5ad4e63eaf17213e9e4f0205978a; original global index 13688.
def localCycle00447 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 0, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle afcff5f5bf1ccfe5a5280d6ef98d13926d03d4af611d01ef1780a1bac5b2f925; original global index 13734.
def localCycle00448 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle afd75eb9c867f94c32cc4acbb004ba782b3846da62936860eae4ef1b07c5eb6e; original global index 13736.
def localCycle00449 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .triangle 29 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle afe1f1ab78b04c74a8971ace8e699178b84e71b5aef63a436ce2dcb8c10e7d6e; original global index 13737.
def localCycle00450 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b06e29c316e64a762ff302289fb93d27b1356d312a76a3228bfbd7ac3b2a9523; original global index 13775.
def localCycle00451 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle b0a65d5ec74dc3d83775ae3456745dfc09969d4a1dace3929e4ec8d8240e7787; original global index 13793.
def localCycle00452 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b1a60cca8237ba2498c5f77f5749202d2dc1de30073d34f320dfae0579accfe2; original global index 13881.
def localCycle00453 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b2243ced871fbb6a79a7cd8c5b9dad3caaeba71e3f056d440758bf489d233d2f; original global index 13920.
def localCycle00454 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b23c98f559201c734df4854455a414f32e0b9a7445beb01aa934f0609bd08e63; original global index 13928.
def localCycle00455 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b271900d5c5feb7a6f303379e1398a05ab52fc4d2977eed1f9b72e4c79ed76ef; original global index 13942.
def localCycle00456 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle b31e754409141f568e22944672c49c754910f9660ec6842870baf39c44f78dd0; original global index 13997.
def localCycle00457 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle b331293ec68091434cbade7f18ee013c4c3173b68a616789c1256fefd6d9a8a1; original global index 14003.
def localCycle00458 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle b46970a2fb60275c75e192e02a9d1728bd6e7680cb9c8d38eb0521c13a5893ec; original global index 14094.
def localCycle00459 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1, .thetaLower 1]

-- Original cycle b4d9ac179e5c66e769dda42b7b6ec26dd394421f0e270f89ddd0dd857dfe5174; original global index 14124.
def localCycle00460 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle b53e941321b72b65a71a06fdcc3de648b4c4b76570fb9162937e4e21ca028f3d; original global index 14161.
def localCycle00461 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b566a3443f7e67c033cda98e21a0b27f9f3d4b0a6c139a1d320092bf54ba5d4f; original global index 14174.
def localCycle00462 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 24 1, .triangle 14 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b62e28e80f495baafe3ace4c9823f4dd53685ffd1830b392aecde7c0744f890f; original global index 14230.
def localCycle00463 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b6401c75363cbddd89b116065eaa57209c83897032a26099433d004fdb1e9e38; original global index 14238.
def localCycle00464 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .corridorLower 2 3]

-- Original cycle b669f99f18700681adc13b3465108b06bc81180ea8d40e4b3abccb8440ce3fa0; original global index 14256.
def localCycle00465 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 7 2, .triangle 14 0, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle b6768a492cbdcbdd8e4b30781e524f145bf930ce8b84bf838477fe6cd94770ab; original global index 14261.
def localCycle00466 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle b681b2d1ec7b2d9438f4d9dca6cb05d62178e0f13f7b573800dad63b743bd5a7; original global index 14263.
def localCycle00467 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle b6d5f7640a90f847dd7c874a9f6c7e0703d3867f43a5ec92d818ccf17806905d; original global index 14285.
def localCycle00468 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b70605d6737ef11b614141fb2554cc9e002190c1a576d519a5c5fc861a6b9fed; original global index 14296.
def localCycle00469 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b7f6deb820e0f0a74c016dee75b85f5d2f90fd1a193d96b7513c7b47c02ee84d; original global index 14354.
def localCycle00470 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3]

-- Original cycle b83116fe62ae00e14e8f85a129982e03264860d2557c2446ada46b81199dd455; original global index 14369.
def localCycle00471 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle b89aff444a567ea4f2a71de918e553b3af2568e8e7d19791da784b7ad2675629; original global index 14404.
def localCycle00472 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle b9a666d932110798b9489f90f08b66f5ed053ae474f8d5931a535fc235953929; original global index 14488.
def localCycle00473 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle b9e9f5cc39fb62169bb42c57c57d6f776afe4de6f82c2f4fcd0263a2f296db78; original global index 14516.
def localCycle00474 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle b9f9fe8a6f35275e5e7e1f58d1736db3e33e49f011174a5cd129be8aa7f37956; original global index 14521.
def localCycle00475 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 4 3, .triangle 29 2, .gapUpper 2 4]

-- Original cycle bb7eed5d4a5ee0e72bae78cb2a9607ce20b2ab3de29e6ee3786a88bd91ee735b; original global index 14635.
def localCycle00476 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 14 1, .triangle 30 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle bb8dd6f237e3b7b320be86bb17ac17b639430b57036e93a518e23dd9e8e90a82; original global index 14640.
def localCycle00477 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 24 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle bbc5d94abd75b89ab3e0fb9f6a8ecf03908fe8e585997711d4035350d3c3adf8; original global index 14664.
def localCycle00478 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle bc25ca7a929d5b4041597da6e7864eeb0463e9f3fc538c55bffad60ee5ca29e9; original global index 14687.
def localCycle00479 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle bc3eb08a15981417d7e8a069c0b612e96ce6e8492749fca448aa6ac501f23752; original global index 14695.
def localCycle00480 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle bcf677990e15cec764b9bc98b6e80c5aafb60c05d90294fac13b0f8d53f35cda; original global index 14743.
def localCycle00481 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle bd9b40e6eb92b4fd7525a2c671417cb4a83f546ff633dab3797266b173c52a76; original global index 14789.
def localCycle00482 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle bdb13c79662b40577a662ad287fe553cb3550a1229ef32f7ff2fe1674fc214eb; original global index 14797.
def localCycle00483 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle bdd3fd1b4e105e8fd226e6131f31d6bdb0f643d582a45411a96078b18562cd45; original global index 14805.
def localCycle00484 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 3 2, .triangle 14 2, .gapLower 6 3, .triangle 29 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle be17bcd633523ae44a74a1b6aaeb23c02e60ddb25f2463561c91b804c67fdfd4; original global index 14825.
def localCycle00485 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle be4782fd5eec3186b1871cf5c487fc4ea18deca1bfd86805ce0b0c807a04e86b; original global index 14840.
def localCycle00486 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 8 1, .triangle 29 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle be7657c1750f534af53523361194aa3a9a33081b44fd79d624909500ddcfcda0; original global index 14858.
def localCycle00487 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle beb91befbaaaf1ce7054f96f8a9d88404146ce0a854a174575ce7c858fa83f64; original global index 14882.
def localCycle00488 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle bebaaf1b81f593c04c6d0a895a9d7084375cd7d2413854a1aa1292a3dd797259; original global index 14883.
def localCycle00489 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .triangle 24 1, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle beeb66f6e7e05bfa794c5ca2757432640c3ef4c25d4e87cafff5c9e181529901; original global index 14894.
def localCycle00490 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 30 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle bfc42ee0633e2b8efaab555b75469ceb8175c6eb64e8444e64711cb9627ed72a; original global index 14963.
def localCycle00491 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .triangle 4 2, .gapLower 6 3, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle c06396193593f8957ee78580a25fa7cc711f71452351561cd82c6f023e1be072; original global index 15018.
def localCycle00492 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c09ac825343842fb040f4f0c3b318a57911aa55a0af5bb90ee530864af9181b9; original global index 15038.
def localCycle00493 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 23 1, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle c142898dfc6f47d74233c96055563e8002d56320b4b67eec3094f0b37b3c6ffa; original global index 15086.
def localCycle00494 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 12 1, .gapUpper 4 3]

-- Original cycle c196da342e06ddb7cf769424a8d264d138c962e997f05f1917bab9d8bafa601f; original global index 15120.
def localCycle00495 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c25008fa6ff2c80fa4d33fd45e28853cabc5bc9ede4d81f2622bc73cbcda5454; original global index 15172.
def localCycle00496 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .triangle 34 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle c2606bebbe346d46f66360e3c9ee272594c3094d1bc8485a7aa0041cffa84159; original global index 15175.
def localCycle00497 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle c265987c688df4b000eb71382661b89c0e2cb1b49bd8e9b9fc952bf7966b3f93; original global index 15178.
def localCycle00498 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle c35803912f8e9243d220aef34f6ce516872bbecee80e1967a55edc78ce49dab7; original global index 15241.
def localCycle00499 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 22 0, .triangle 23 0, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle c4f04edad64ce4dfd0de70f1a4be670bde7e0477b28716c97c6a5a3c7275c732; original global index 15369.
def localCycle00500 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c512d217666a5e0e84ce82619b77aad5fb16b4caa90552b3934600e0f145892a; original global index 15377.
def localCycle00501 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle c52e7436dbe7b66e1f12ba69130b7fdbd29c0ca6142e1a72cbeafd901172cddf; original global index 15383.
def localCycle00502 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c570e95a05648a96f8713e43100edc4540798680b68fdc65037d7b53861f3126; original global index 15404.
def localCycle00503 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 2, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle c575ae2e78c46752c463fce168d1d6cc101b4120fcb81bd79dbc57ad9e515081; original global index 15407.
def localCycle00504 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle c57b885b50ca1192f81b4484dbb767f0cb0ff6a357a198959932172df6d1a0e6; original global index 15408.
def localCycle00505 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, -3, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 22 0, .triangle 23 0, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle c610d7abf406ec57b70c18a4a4fde3bb3875a887da8cceb95f77ebbb092cc65d; original global index 15448.
def localCycle00506 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .gapLower 0 1]

-- Original cycle c618dc47c9f3df00e620d9c15e8a266e47fe90e331dfe95a2b371b63b131877e; original global index 15452.
def localCycle00507 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle c7dd13ea82b39a4b02130c51a58dde004c69c57a49997524bec79eb1556213a7; original global index 15605.
def localCycle00508 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 6, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 13 2, .gapLower 0 3, .gapLower 5 2, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle c7ee013a7502bf2f19cf7c639e12dd86bf97d394e8025f018c70cd231d379c1d; original global index 15608.
def localCycle00509 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle c821137f55393101e88947f44e2671fa85c5a68c000c23b14f71ff3f7a4dd8d2; original global index 15623.
def localCycle00510 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle c905d8990c233d901335e7d27ea420c35b3f9dfaa7a93498e048635dfbdc442a; original global index 15701.
def localCycle00511 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle ca02a9987ed52b1e3328b07e61275467130fdfcb36bcc47e2bed199983562ed2; original global index 15789.
def localCycle00512 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 3, .triangle 29 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle caf096fe971f690bc9301d0b3c3e971c149c079cb8a74cbf1402257cc23ac30c; original global index 15856.
def localCycle00513 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle caf1b77b7a299a3f3dbde4a958be7513686a2dbe852427f471faed2ec91dfa99; original global index 15857.
def localCycle00514 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle cb01fd46c945f7f6b311b99522091881fc4e272c6cc6580b782e0bc46cb5592b; original global index 15861.
def localCycle00515 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 34 0, .corridorLower 4 5]

-- Original cycle cb4ca35426ffc13c3db07e710765d6b9602a266cf0ec7c9b5c7113e0208c47eb; original global index 15879.
def localCycle00516 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle cb9d8168d43625b8b542ca72015183691353c2a8bab6f8a909220c15292f1fe8; original global index 15910.
def localCycle00517 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .triangle 24 2, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle cbde80105868601f68fca78f1db0cbbb43d22543cd3bda6d72794a5f0c80b967; original global index 15932.
def localCycle00518 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 23 1, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cd07175d33f48d5df63460278663f0a2d346440fe605357ef3e5213096b9a7f7; original global index 16023.
def localCycle00519 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle cd60bef3d0fd3803cb4da00507f2988afc91a8b2ceb971d0e4f61bad07b162bf; original global index 16052.
def localCycle00520 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle ce08e10ba4812c59b68e295ffb5aa347376373c475db622311f26c01142e6cb8; original global index 16097.
def localCycle00521 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 5 0, .triangle 26 0, .gapLower 5 0]

-- Original cycle ce3087a7d85fdcd4563b51b5cdd0c5b14caed2c914b30ab7d4b4d4eedc5e509e; original global index 16108.
def localCycle00522 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cf29a623ae84105f8f423a806278fa1d666e3062ee7b652343acfcda22f331f2; original global index 16167.
def localCycle00523 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle cf29bdba80f64e003006005ce22bac7fcca2828b0391c990658cbd2d4729cb41; original global index 16168.
def localCycle00524 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cf2f3ee20c922be141e78b2c273f884f7bc1e01d2441d57aa95f51c64697d56c; original global index 16171.
def localCycle00525 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .triangle 29 1, .gapLower 4 0]

-- Original cycle cf8c657dd1b66e9e89896b1434864b0c69e1d609b48d2c4ee950cbf2519fa678; original global index 16192.
def localCycle00526 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle cf9397d1d913cf5c4ec5ea2ff4ee9afecb689982ea7b804fcdd28ba84f1fb92d; original global index 16194.
def localCycle00527 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cfb8e2544ec97e0ea43942dc5b696a695f44cd3a6e3cb7e4954e763be5d23a97; original global index 16211.
def localCycle00528 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .triangle 32 1]

-- Original cycle cfdf632fb896d5def6809e632b108f25c90fab266357ae3a5076963a2739348c; original global index 16221.
def localCycle00529 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d01c5d09c03d0347f6dcedb2d82a760d2e2e64c27803481c44804e32dccbb722; original global index 16244.
def localCycle00530 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d057ba840b77f349e4aa366edbf8803b5eef688feb9932e7a0a89969ccec9dd2; original global index 16261.
def localCycle00531 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 21 1]

-- Original cycle d0cd5597c359a16bc4cf2418755b9f24013afd27f3a947f110a5e6345ff2ab4f; original global index 16299.
def localCycle00532 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d0e45343a60d83385d73e0d9379473b98d3ffb007c61fa20a945ab4e74353d2e; original global index 16311.
def localCycle00533 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle d0fff44e2a98cecc24126cc3f8cf094f12a7542b3b1e3426de0a7e730014bb29; original global index 16319.
def localCycle00534 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 28 0, .corridorLower 4 5]

-- Original cycle d1aefdb7d85d914217d2b220cd7b0d6e934ad69b9514b47bb920b2cedd7e4293; original global index 16366.
def localCycle00535 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d1e3ab5e70d293eac61af6b7c0a8370af9c81cd24f1fc7d0e1cf98a99c2380b3; original global index 16381.
def localCycle00536 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d3a783478eab03865e1b39122748ba7c9a64d6e0a6d4aa11695d526e74c73e6c; original global index 16514.
def localCycle00537 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle d4003c6a03d31972b032f0f8539ea45837388ad4a14458ff114d9a0b67259e47; original global index 16546.
def localCycle00538 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 29 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle d46507faaec9581ee857c0e6d86e7e6a72ccc8c06aed28cfc82d49478e9dda9b; original global index 16573.
def localCycle00539 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -2, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 2, .triangle 24 0, .triangle 14 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle d512aee029732d5e0ead23e255433a856d40e9693220434bc05779ab8e607a5a; original global index 16627.
def localCycle00540 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle d56e7d47b4f4cc26ad56d529fd7e7e42887db97ffbd4e08d322cebfc044e0f38; original global index 16661.
def localCycle00541 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 9 0, .triangle 5 1, .corridorLower 2 3]

-- Original cycle d61d13a7fa09ed7d5065e8daad133c36e52bd844799ae3cc7ae3bc30aa4d3a8f; original global index 16714.
def localCycle00542 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle d632c33ed058fd922f00f5976987b84fc16661bb4d45c01f3c9dcbc684fb1f4d; original global index 16721.
def localCycle00543 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 4, .gapUpper 4 3]

-- Original cycle d67cea04378cc0b15b3bbf149e9f58d63c2fe54b8c880ee567e137c7838c7574; original global index 16743.
def localCycle00544 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle d6b9768d0908b6ae3b3e7a7ef2565d293be9f2b5c4b88a0f64ce27b8d9628906; original global index 16760.
def localCycle00545 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 30 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle d6ccafa3f9e3d6b18b22e13d1d3b762ceee577978fec50acf09ae4d08576a71e; original global index 16769.
def localCycle00546 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle d78aa84bcfa72f513f1f161695a01f92e94e15ab3a4f8a8e6136a4c9de6ff9bc; original global index 16820.
def localCycle00547 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle d82e4fa93d7f5a87f880989717c75d01b1beeeb8e2285763c8ae9fb3bacfd01c; original global index 16876.
def localCycle00548 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 2, .triangle 24 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle d840d61db4573497ad807cae18a2666ccbca07f2856aa75b9f270eeff28b122a; original global index 16880.
def localCycle00549 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle d8a417dd2532b26b67f7696766aed495dd8dc031f3368d94f26c88ee410dd1af; original global index 16909.
def localCycle00550 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .triangle 4 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d9392e02fa5938a6f4535c2dd7c8a6090a912c2ce9bb92a35a02d6c340ba698c; original global index 16972.
def localCycle00551 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 23 1, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d94d8f18678d9f17c847ffc7cc8c703dce6e67425003698ceef1c96dc1604aa6; original global index 16979.
def localCycle00552 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 23 0, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle d9a037af7a88065c09d601b8309bcb333da7a1c755419d5bd09781b7f941da5d; original global index 17002.
def localCycle00553 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 34 0, .corridorLower 4 5]

-- Original cycle da31917b5a1989e7ab143e0f4be9ea928de3d1ecf6766723c588a412e391f424; original global index 17048.
def localCycle00554 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle da63a282cb4dc5c620cf3644ae36bf2cfa380c1398e82b865b25cda0a802223b; original global index 17065.
def localCycle00555 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 0, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle da98ab881514e09c15b15aaa493a72a6978a6890149fd5567746fac769daae0d; original global index 17084.
def localCycle00556 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 24 2, .gapLower 6 3, .triangle 14 2, .gapLower 6 1, .triangle 29 1, .gapLower 4 0]

-- Original cycle dafa7a0d1453d755769c7418443c4f59510d5369a3ef5701f819b27952b96aa9; original global index 17112.
def localCycle00557 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 23 0, .gapLower 1 2]

-- Original cycle db11259053b4b6e73ca604ea96754e1932b4c810a74faccd09ef874f12fd8b11; original global index 17118.
def localCycle00558 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .triangle 4 2, .gapLower 6 3, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle db13d0adf9c4386e66adc12354fe73f39ac9c5f37826e41e6d19978997d535b4; original global index 17120.
def localCycle00559 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle dbe7a26dc95ff77d94e468bfeb132de7a57024e255101a27a6124ca4406c0276; original global index 17187.
def localCycle00560 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 0 5, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 8 2, .gapLower 0 4, .corridorLower 0 5]

-- Original cycle dbf915d41c26af1817670e3fcd289f713a3ccd5a39409d28d2f96f457c421f34; original global index 17194.
def localCycle00561 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle dc10a19fdbd3649fcd27375ebac33664bdad554f68c4fc0a1f75a832c81c3bd0; original global index 17200.
def localCycle00562 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle dc9d78b5682815e50cd6c1c2ffb1cee7d154a2bac80f2ff9be2d0590f4fe043a; original global index 17234.
def localCycle00563 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 2, .triangle 30 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle dcbbe4fa9608bd467eef6dc42d83cc8e733d175bf10e9b99af9109760a68b1b8; original global index 17246.
def localCycle00564 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 2, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 29 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 5 1, .corridorLower 2 3]

-- Original cycle dd8769e344823aa8a7b7c6cfb68ba4e3335784c4804f74b830e7241e59cbfb7b; original global index 17319.
def localCycle00565 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle ddf495f2d4d85ad3bbdf096a3f67dbd01fce13f0215287c7df7ceef4214a40f1; original global index 17351.
def localCycle00566 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 30 0, .gapLower 2 2]

-- Original cycle de169ed1f88c3d5618a77055d196324856f9319afde536c9bfefc6a2ed4d0413; original global index 17369.
def localCycle00567 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle de5f761374a630e8403a02c90d440fd601768e629a2545dbfa0af8ee353a45a8; original global index 17384.
def localCycle00568 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle de887bbcb918d144c803941576c0ab899080e7e84ec53666772e6d41cd53ffb9; original global index 17399.
def localCycle00569 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle de8ef3c95dc57d22a123e0be994477a5ab545e215a0a77f7b7a504f7f4771a92; original global index 17402.
def localCycle00570 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle deb755e3ff136db83402d95da37e8d51e92cac4a2b8d24009b7146f84244a2c0; original global index 17412.
def localCycle00571 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 21 2, .triangle 4 2, .gapLower 6 2, .triangle 29 1, .gapLower 6 0]

-- Original cycle df0aea2ddd88493b530f2b9293cbe39f42944ef336a5dcaa7b623f87b770c56f; original global index 17434.
def localCycle00572 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle df7493af30b36816747c2f4fe25375180d182c152a40844123756eb2e6f857ee; original global index 17462.
def localCycle00573 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle df7ebab74ff409eec595e81f978bb6955fde8c600d34917c58bcd1c52500442d; original global index 17465.
def localCycle00574 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 14 1, .triangle 30 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e0ae65ae1a807027f3215599e1be31b3a967b662b69be1911bc3031043ce6e23; original global index 17569.
def localCycle00575 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 14 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e0c69ebb151603ea799459b7a0d52a0018170e3a17e8c54fda592dd930b2b66d; original global index 17575.
def localCycle00576 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle e0d8322bdf84aa29c74a2874f1f034b0688476c87851de549852bafc614f47c0; original global index 17579.
def localCycle00577 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 13 1, .gapUpper 4 3]

-- Original cycle e12331ce7004fdbb8c85f75fa2275e24930437814a830a01523ac1ecf9abf835; original global index 17603.
def localCycle00578 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 6 0, .triangle 29 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaLower 5]

-- Original cycle e2f0c705c609eb2328bca722074275b9bdb45bcd93e5b55001afc6f44db43441; original global index 17750.
def localCycle00579 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle e31902ca165b5d90be7f919d7525d227e25b902e99e6d08225e0e905eed4370d; original global index 17758.
def localCycle00580 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e345e9c51b85e97d0137c875667b87d7e0b09a947945f2bd4967259ca3085f42; original global index 17773.
def localCycle00581 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle e37636d2591d7bbb298c216a14dde19aba0f2dee433b22095ed52186c0739d12; original global index 17789.
def localCycle00582 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 30 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle e3bb372fcaef8247878717490c8f26bc94ed1f985ca2a550f0d269b1906481de; original global index 17808.
def localCycle00583 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 24 1]

-- Original cycle e3bb45b3b3de922503081466693756c57fa82fe59b08e7618bf6b661f20c403c; original global index 17809.
def localCycle00584 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 4, .distance 2 4, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .gapLower 0 3, .gapLower 4 1, .gapLower 4 0]

-- Original cycle e54969756ac5a47c52331cae3c8b57bc217c4d7e4916c9e10936146e32659d12; original global index 17926.
def localCycle00585 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle e5c45ffa1c31641538ad72c78e94d4474e232c1f6da30cf7b67bc669662e418f; original global index 17976.
def localCycle00586 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle e5c74f634d73578553f445b6300f25676daf479e03771e57c6c1c68c8a678d8f; original global index 17978.
def localCycle00587 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 14 1, .triangle 30 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e622a2193f2d51c536c42e3c5c8b33f10aa21d2cdd2219170c37419a6af9235d; original global index 18009.
def localCycle00588 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e75d2b98524df338823c4cdd814b97b65b44f1e04d02738f671c0d024b91d8f9; original global index 18097.
def localCycle00589 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 8 1, .triangle 29 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e79ed1f0669e3723b554d7fe3976dcc7d449728d7ddfa8d6ed1d4c17f96f87b6; original global index 18116.
def localCycle00590 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 2, .gapLower 6 3, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle e8668f5e2b18beb3bc493635d1fd1b0002a7b57ec88ad65962db23e638255b74; original global index 18167.
def localCycle00591 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .gapLower 4 2, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle e8d4200a0eea7e8dd7480da2abe31f1bda44dd214edd95006aef4ad52bb8dd65; original global index 18197.
def localCycle00592 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .triangle 14 1, .triangle 30 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e8ffd1297463927cd481154d37f2f354d628053aad2df2e3d65939e7debc3f30; original global index 18209.
def localCycle00593 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle e949641e6afe75aef36db8fb06363c5cacc57cbbcacf6f1697903a0ac876e239; original global index 18230.
def localCycle00594 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 9 1, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e9cd8cb2e67df551765e7c9adcb741e69c78d54da1c02cb3f69aa8ed61050b2f; original global index 18268.
def localCycle00595 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 0 3, .triangle 10 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle e9e2b3f3c79b1310327824dbdf8ab79c0649162c98a0f1caf00030d6375f80c8; original global index 18275.
def localCycle00596 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .gapLower 4 0]

-- Original cycle ea0781fb605d308182422247566cac8de690a4db14c079bc9e18838501ace7a8; original global index 18282.
def localCycle00597 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle ea268c3dd54347123d5710396e162ac84936811fb5b1d69098810dffe473c181; original global index 18290.
def localCycle00598 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 5, .distance 0 2]
    constant := ![-2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 0 4, .gapLower 5 3, .triangle 28 2, .gapUpper 2 4]

-- Original cycle eba5a17ee8f9d2b130b05e699f5a04399e6823353739202a8529e504e28e1586; original global index 18386.
def localCycle00599 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle ecf6ddb9936bc7d7d7078b04e87c6983a221aeb60d667fc9ea9b1a472a8c22e9; original global index 18497.
def localCycle00600 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle ed6a65e007e6543e0c07ab4993e8a99e86bb54486da5e4f117b6594e101aebe6; original global index 18533.
def localCycle00601 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle eda8675a1db600f332bf0a4ca24f90d1ba55c5a4ef79a0ed78b52eb216ef7803; original global index 18553.
def localCycle00602 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -3, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle ee4bed3390fae9ea600c14c36613854832ff0b2633ac942d61997e33c9e9256f; original global index 18598.
def localCycle00603 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle ee68eba6c8d2e49d7dac37cc4c7a6eb7dc862a8406665129a801c11666797bcf; original global index 18611.
def localCycle00604 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle eef0b1baceffd57988fb21912a8464a4554d5e9abbb6b288abb6ae33c9ff2e54; original global index 18646.
def localCycle00605 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle ef359d6a921883259a470523333ac2f6b2fd6ad61a84b061483e37eebbab3f23; original global index 18663.
def localCycle00606 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle ef38b68ff0c033da010383c6fa07dc940300b51c338ab88f18eff8e1e21d40cf; original global index 18664.
def localCycle00607 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle ef6a8dcc8e97edb36e6fd545fbc59a2fa590874fc4eefd3b340c1823846ecd18; original global index 18681.
def localCycle00608 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.triangle 13 0, .gapLower 6 2, .gapUpper 5 2, .triangle 12 1]

-- Original cycle efc9535f65b4ff39fce6db20a315d2ff42b3fa5f2b9d75719f5a6c2713b7e6db; original global index 18708.
def localCycle00609 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 5 6, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![2, 2, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.gapUpper 3 3, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 23 0, .gapLower 1 2]

-- Original cycle efe6065c7b65103eafc4681f962a17b7cec0e512bb4ff46ab456640ae08415f3; original global index 18717.
def localCycle00610 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 23 1, .triangle 34 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle efece806fb2273190b330561ea148cb6c7fd69c0d79dc596b8d8f11572ef899c; original global index 18720.
def localCycle00611 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 0, .gapLower 6 2, .triangle 8 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle efedfbc838987017e25cfa848a3ded288ba914fda5e852e35056e813d0ae26e8; original global index 18722.
def localCycle00612 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 2, .triangle 14 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle f002850e4790ea8e86f8e1747178d8a9c8523062804652aa588857382d6ecbdc; original global index 18726.
def localCycle00613 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f003cf6e1065cdf3e194f17b63e495f7835599e11e660c820e9ebbf7378b0e06; original global index 18727.
def localCycle00614 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![4, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .triangle 29 1, .triangle 28 0, .corridorLower 4 5]

-- Original cycle f0a9824bda98e96d1af51cdb4ae5de3999ca7bcd40212e871e3f122c19ce08e6; original global index 18770.
def localCycle00615 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle f0b13a0b1eb380f899d16deb10cbdc87726031974be1de7546e56ff992ced400; original global index 18775.
def localCycle00616 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 6 2, .triangle 13 0, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle f0c1949588c72ceb22408a2ab331e7ef1942151cb446edea11d268dcc6d0ff8a; original global index 18778.
def localCycle00617 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 29 1, .gapLower 4 0]

-- Original cycle f0cff70a8d571016241bb0bb9d8e7284295875ca3a7b08853799ff7674bcdddc; original global index 18782.
def localCycle00618 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle f14c40b916271c95d300e4f3346cf5c7f12b12a9dcdca2f4cb4519a4abf4edb4; original global index 18815.
def localCycle00619 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .gapLower 0 1]

-- Original cycle f1e7d6ab6cf2ca9646f9912c6a45900352c953b78b6f308b984890de3c205e75; original global index 18865.
def localCycle00620 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle f22c6d50f449251e055472f4f678a697710546ab34b65d004ecd3c6d02781fbe; original global index 18887.
def localCycle00621 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .gapLower 5 3, .gapLower 0 4, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle f245941335114c1d6583367a40064eaa998e1117fc1dd02bd969bf3f7b1a726a; original global index 18893.
def localCycle00622 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle f277eb11fd0500d98da741b61ecea54faaea400c7149e34e2dc7195bb90b021e; original global index 18904.
def localCycle00623 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

-- Original cycle f2a37334d8830111f4f41f72b9f5b78d4eb4f41a2380f9b8f9596543c26e8085; original global index 18915.
def localCycle00624 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle f2c9bbeedec050fec0250a852de4885951f3f7686825be4df8aedfddb0eab402; original global index 18925.
def localCycle00625 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle f2e9a76176978d73f8ec11d98ce2ec3a3633e9a13bc4ed0897c78388a4f61cde; original global index 18935.
def localCycle00626 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle f3330fd86917263505d737800306ea4127135737ff5dfda5a04a00432c4dbe13; original global index 18964.
def localCycle00627 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f363475ca38ad94db4df2c5108ca5782ef8e270c9c95da058edb970392a46013; original global index 18984.
def localCycle00628 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 13 1, .triangle 29 2, .gapLower 6 0]

-- Original cycle f372f26a486974945690025e093a62205894698a1c57a80d3bf345add001ddcd; original global index 18990.
def localCycle00629 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 8 1, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle f3f36aa99721690ddb169e61aadce8c1784982cda8622000f8516034be75b3c4; original global index 19024.
def localCycle00630 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 29 1, .gapLower 6 0]

-- Original cycle f4bc5fee54cfd5c2eb5cd0575a62c4914ae06558bc2fb4a839c63ac082c62f0c; original global index 19076.
def localCycle00631 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle f5a88cc8f0a70d68788d157f73d60d8bd48567f688833a741a7485959f9ded34; original global index 19157.
def localCycle00632 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle f5e629243e486ccc4fe9a96d46c7eddcdfe10d01aec7cf4f9fc82822b6f11c93; original global index 19187.
def localCycle00633 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle f6be143f600dc198c1cedb182796ec692265e437c5dc492d8d12b1ea2cf2ec26; original global index 19250.
def localCycle00634 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 4 2, .triangle 13 2, .gapLower 0 3]

-- Original cycle f6d7e776a3837fff6ee313a7219ffc190400e21f21cc3e6aca7e216749cdc762; original global index 19253.
def localCycle00635 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 3 2, .triangle 32 1, .triangle 13 0, .gapLower 0 2]

-- Original cycle f7120f88d5477532f32589c407be29c3d0a469049e5ce71adc924963ebe8c425; original global index 19268.
def localCycle00636 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, 0, -2, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, true, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 14 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle f7b9b05095465acc8418d5f1e3779aac94d094f8fbfc3e341f6993b2fe79979e; original global index 19313.
def localCycle00637 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 0, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f8261c63b5f82ba998e4f277d02b97c7dcfda20b44e651d7763bb51cf5608292; original global index 19350.
def localCycle00638 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 33 1, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f8b00d9948b33d9513e79d0fc4e1d8f18a068803885de86edc4a62475f434160; original global index 19393.
def localCycle00639 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 34 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle f8fdfe5794f5b836f7b3d4b72c4faaace303bc4730f05af5e50d68987398767c; original global index 19418.
def localCycle00640 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f93384087dc2a75f6a8ec17a89cf4dee2506f641e1868e880360504fe3446dc9; original global index 19435.
def localCycle00641 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 12 2, .gapLower 0 3, .triangle 13 1, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle f956dc34831161cf9c754f89e5244e04456d02e5bf3a32cad897da9b8f6e21b8; original global index 19443.
def localCycle00642 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle f9c869b006469b183fb6ae92751bad06e3131eeb16280f8607ea093a7971a6cf; original global index 19478.
def localCycle00643 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle fa3f0973e4e4049660bbff39e5a7849a43aa5954c448dcfe16d31a96497fcb93; original global index 19517.
def localCycle00644 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .triangle 14 2, .triangle 8 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle faefbb344dddc46dd2644fde3e196589ca63a49258fbb37238b9fc3b5853a461; original global index 19584.
def localCycle00645 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle fba684ea7fdc07a92a5e9e6ea3e81cea83ea53d468c44bcd228c0fec5ce60dd6; original global index 19646.
def localCycle00646 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .triangle 14 1, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle fbbdde47fd266cad8b0a59d5f63578f07180f97d64778ec54eeb17e96e11f10f; original global index 19652.
def localCycle00647 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 6 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle fbbeef991e6ddeaacc1ddf1126cb96343fc3119439a6afd1cd7ffd5a7acaed18; original global index 19653.
def localCycle00648 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 1, .triangle 24 0, .triangle 20 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fbedcb0e080267cac12953d6816bbded75aaefa605b69dc8093f1e31f163fe86; original global index 19668.
def localCycle00649 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle fc2201084ab1f7a8ebde0e086ac53c4c09dc0be4ee7757a33841c40161b290c3; original global index 19688.
def localCycle00650 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle fd20528e7ab839923f8ecbcf0434e47ba5ca57956b1cbff7eabad88c9cf9fde5; original global index 19780.
def localCycle00651 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 2 4]
    constant := ![2, 0, -3, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 4 1, .triangle 34 1, .gapLower 6 1, .triangle 29 1]

-- Original cycle fe0d15375d56cf16cf430f2fe7e37592088d2989d18c195d766101f3ef598d15; original global index 19853.
def localCycle00652 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle fe37fb6f3c50e5058105329eaf1efde927fe99649238014b919cd244ceb742e4; original global index 19870.
def localCycle00653 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 29 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle fe3c7df266e1b598a8869ccdcc9498b3bd33fe228fd2201ea49a68be57cbd826; original global index 19873.
def localCycle00654 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle fe899064a0bdca341c364458728d5caf62b75357c873e3ee31b6265d807ed8fc; original global index 19897.
def localCycle00655 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 29 2, .gapLower 6 0]

-- Original cycle fea000a3caffa86cad0a868617505754712428ec107133dd2b1dacacc036e926; original global index 19907.
def localCycle00656 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle feba907811fa2610acf572dc98dccf1c9bbd51fa519d1c672750558e0379557e; original global index 19918.
def localCycle00657 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle ff6dc82f3713a1da9272d22eb0a773ba34ce825c2b74d74d1efe94e5a34127d3; original global index 19970.
def localCycle00658 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, 2, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle ffb2aecab56c352205dabeacd764665db711b391b80a0ed7e535411313632fbe; original global index 19998.
def localCycle00659 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 0, .triangle 14 2, .gapLower 6 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5]

def library : Library := fun id => if id < 330 then (if id < 165 then (if id < 82 then (if id < 41 then (if id < 20 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 17 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))))) else (if id < 30 then (if id < 25 then (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))))) else (if id < 35 then (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))))))) else (if id < 61 then (if id < 51 then (if id < 46 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))) else (if id < 56 then (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)))))) else (if id < 71 then (if id < 66 then (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))) else (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))))) else (if id < 76 then (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))) else (if id < 79 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))))))) else (if id < 123 then (if id < 102 then (if id < 92 then (if id < 87 then (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))))) else (if id < 97 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))))) else (if id < 112 then (if id < 107 then (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))) else (if id < 117 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))) else (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))))))) else (if id < 144 then (if id < 133 then (if id < 128 then (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)))) else (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))))) else (if id < 138 then (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)))) else (if id < 141 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)))))) else (if id < 154 then (if id < 149 then (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))) else (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))))) else (if id < 159 then (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)))) else (if id < 162 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))))))))) else (if id < 247 then (if id < 206 then (if id < 185 then (if id < 175 then (if id < 170 then (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)))) else (if id < 172 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))))) else (if id < 180 then (if id < 177 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)))))) else (if id < 195 then (if id < 190 then (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)))) else (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none))))) else (if id < 200 then (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)))) else (if id < 203 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))))))) else (if id < 226 then (if id < 216 then (if id < 211 then (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none)))) else (if id < 213 then (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none))))) else (if id < 221 then (if id < 218 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)))) else (if id < 223 then (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)))))) else (if id < 236 then (if id < 231 then (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none)))) else (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none))))) else (if id < 241 then (if id < 238 then (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none)) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)))) else (if id < 244 then (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none))) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none)))))))) else (if id < 288 then (if id < 267 then (if id < 257 then (if id < 252 then (if id < 249 then (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none)) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id = 251 then some localCycle00251 else none)))) else (if id < 254 then (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none)) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id = 256 then some localCycle00256 else none))))) else (if id < 262 then (if id < 259 then (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id = 258 then some localCycle00258 else none)) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none)))) else (if id < 264 then (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id = 263 then some localCycle00263 else none)) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none)))))) else (if id < 277 then (if id < 272 then (if id < 269 then (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none)) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none)))) else (if id < 274 then (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none)) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none))))) else (if id < 282 then (if id < 279 then (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id = 278 then some localCycle00278 else none)) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none)))) else (if id < 285 then (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id = 284 then some localCycle00284 else none))) else (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id = 287 then some localCycle00287 else none))))))) else (if id < 309 then (if id < 298 then (if id < 293 then (if id < 290 then (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id = 289 then some localCycle00289 else none)) else (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id = 292 then some localCycle00292 else none)))) else (if id < 295 then (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id = 294 then some localCycle00294 else none)) else (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id = 297 then some localCycle00297 else none))))) else (if id < 303 then (if id < 300 then (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id = 299 then some localCycle00299 else none)) else (if id < 301 then (if id = 300 then some localCycle00300 else none) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id = 302 then some localCycle00302 else none)))) else (if id < 306 then (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id = 305 then some localCycle00305 else none))) else (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id = 308 then some localCycle00308 else none)))))) else (if id < 319 then (if id < 314 then (if id < 311 then (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id = 310 then some localCycle00310 else none)) else (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id < 313 then (if id = 312 then some localCycle00312 else none) else (if id = 313 then some localCycle00313 else none)))) else (if id < 316 then (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id = 315 then some localCycle00315 else none)) else (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id = 318 then some localCycle00318 else none))))) else (if id < 324 then (if id < 321 then (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none)) else (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id < 323 then (if id = 322 then some localCycle00322 else none) else (if id = 323 then some localCycle00323 else none)))) else (if id < 327 then (if id < 325 then (if id = 324 then some localCycle00324 else none) else (if id < 326 then (if id = 325 then some localCycle00325 else none) else (if id = 326 then some localCycle00326 else none))) else (if id < 328 then (if id = 327 then some localCycle00327 else none) else (if id < 329 then (if id = 328 then some localCycle00328 else none) else (if id = 329 then some localCycle00329 else none)))))))))) else (if id < 495 then (if id < 412 then (if id < 371 then (if id < 350 then (if id < 340 then (if id < 335 then (if id < 332 then (if id < 331 then (if id = 330 then some localCycle00330 else none) else (if id = 331 then some localCycle00331 else none)) else (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id < 334 then (if id = 333 then some localCycle00333 else none) else (if id = 334 then some localCycle00334 else none)))) else (if id < 337 then (if id < 336 then (if id = 335 then some localCycle00335 else none) else (if id = 336 then some localCycle00336 else none)) else (if id < 338 then (if id = 337 then some localCycle00337 else none) else (if id < 339 then (if id = 338 then some localCycle00338 else none) else (if id = 339 then some localCycle00339 else none))))) else (if id < 345 then (if id < 342 then (if id < 341 then (if id = 340 then some localCycle00340 else none) else (if id = 341 then some localCycle00341 else none)) else (if id < 343 then (if id = 342 then some localCycle00342 else none) else (if id < 344 then (if id = 343 then some localCycle00343 else none) else (if id = 344 then some localCycle00344 else none)))) else (if id < 347 then (if id < 346 then (if id = 345 then some localCycle00345 else none) else (if id = 346 then some localCycle00346 else none)) else (if id < 348 then (if id = 347 then some localCycle00347 else none) else (if id < 349 then (if id = 348 then some localCycle00348 else none) else (if id = 349 then some localCycle00349 else none)))))) else (if id < 360 then (if id < 355 then (if id < 352 then (if id < 351 then (if id = 350 then some localCycle00350 else none) else (if id = 351 then some localCycle00351 else none)) else (if id < 353 then (if id = 352 then some localCycle00352 else none) else (if id < 354 then (if id = 353 then some localCycle00353 else none) else (if id = 354 then some localCycle00354 else none)))) else (if id < 357 then (if id < 356 then (if id = 355 then some localCycle00355 else none) else (if id = 356 then some localCycle00356 else none)) else (if id < 358 then (if id = 357 then some localCycle00357 else none) else (if id < 359 then (if id = 358 then some localCycle00358 else none) else (if id = 359 then some localCycle00359 else none))))) else (if id < 365 then (if id < 362 then (if id < 361 then (if id = 360 then some localCycle00360 else none) else (if id = 361 then some localCycle00361 else none)) else (if id < 363 then (if id = 362 then some localCycle00362 else none) else (if id < 364 then (if id = 363 then some localCycle00363 else none) else (if id = 364 then some localCycle00364 else none)))) else (if id < 368 then (if id < 366 then (if id = 365 then some localCycle00365 else none) else (if id < 367 then (if id = 366 then some localCycle00366 else none) else (if id = 367 then some localCycle00367 else none))) else (if id < 369 then (if id = 368 then some localCycle00368 else none) else (if id < 370 then (if id = 369 then some localCycle00369 else none) else (if id = 370 then some localCycle00370 else none))))))) else (if id < 391 then (if id < 381 then (if id < 376 then (if id < 373 then (if id < 372 then (if id = 371 then some localCycle00371 else none) else (if id = 372 then some localCycle00372 else none)) else (if id < 374 then (if id = 373 then some localCycle00373 else none) else (if id < 375 then (if id = 374 then some localCycle00374 else none) else (if id = 375 then some localCycle00375 else none)))) else (if id < 378 then (if id < 377 then (if id = 376 then some localCycle00376 else none) else (if id = 377 then some localCycle00377 else none)) else (if id < 379 then (if id = 378 then some localCycle00378 else none) else (if id < 380 then (if id = 379 then some localCycle00379 else none) else (if id = 380 then some localCycle00380 else none))))) else (if id < 386 then (if id < 383 then (if id < 382 then (if id = 381 then some localCycle00381 else none) else (if id = 382 then some localCycle00382 else none)) else (if id < 384 then (if id = 383 then some localCycle00383 else none) else (if id < 385 then (if id = 384 then some localCycle00384 else none) else (if id = 385 then some localCycle00385 else none)))) else (if id < 388 then (if id < 387 then (if id = 386 then some localCycle00386 else none) else (if id = 387 then some localCycle00387 else none)) else (if id < 389 then (if id = 388 then some localCycle00388 else none) else (if id < 390 then (if id = 389 then some localCycle00389 else none) else (if id = 390 then some localCycle00390 else none)))))) else (if id < 401 then (if id < 396 then (if id < 393 then (if id < 392 then (if id = 391 then some localCycle00391 else none) else (if id = 392 then some localCycle00392 else none)) else (if id < 394 then (if id = 393 then some localCycle00393 else none) else (if id < 395 then (if id = 394 then some localCycle00394 else none) else (if id = 395 then some localCycle00395 else none)))) else (if id < 398 then (if id < 397 then (if id = 396 then some localCycle00396 else none) else (if id = 397 then some localCycle00397 else none)) else (if id < 399 then (if id = 398 then some localCycle00398 else none) else (if id < 400 then (if id = 399 then some localCycle00399 else none) else (if id = 400 then some localCycle00400 else none))))) else (if id < 406 then (if id < 403 then (if id < 402 then (if id = 401 then some localCycle00401 else none) else (if id = 402 then some localCycle00402 else none)) else (if id < 404 then (if id = 403 then some localCycle00403 else none) else (if id < 405 then (if id = 404 then some localCycle00404 else none) else (if id = 405 then some localCycle00405 else none)))) else (if id < 409 then (if id < 407 then (if id = 406 then some localCycle00406 else none) else (if id < 408 then (if id = 407 then some localCycle00407 else none) else (if id = 408 then some localCycle00408 else none))) else (if id < 410 then (if id = 409 then some localCycle00409 else none) else (if id < 411 then (if id = 410 then some localCycle00410 else none) else (if id = 411 then some localCycle00411 else none)))))))) else (if id < 453 then (if id < 432 then (if id < 422 then (if id < 417 then (if id < 414 then (if id < 413 then (if id = 412 then some localCycle00412 else none) else (if id = 413 then some localCycle00413 else none)) else (if id < 415 then (if id = 414 then some localCycle00414 else none) else (if id < 416 then (if id = 415 then some localCycle00415 else none) else (if id = 416 then some localCycle00416 else none)))) else (if id < 419 then (if id < 418 then (if id = 417 then some localCycle00417 else none) else (if id = 418 then some localCycle00418 else none)) else (if id < 420 then (if id = 419 then some localCycle00419 else none) else (if id < 421 then (if id = 420 then some localCycle00420 else none) else (if id = 421 then some localCycle00421 else none))))) else (if id < 427 then (if id < 424 then (if id < 423 then (if id = 422 then some localCycle00422 else none) else (if id = 423 then some localCycle00423 else none)) else (if id < 425 then (if id = 424 then some localCycle00424 else none) else (if id < 426 then (if id = 425 then some localCycle00425 else none) else (if id = 426 then some localCycle00426 else none)))) else (if id < 429 then (if id < 428 then (if id = 427 then some localCycle00427 else none) else (if id = 428 then some localCycle00428 else none)) else (if id < 430 then (if id = 429 then some localCycle00429 else none) else (if id < 431 then (if id = 430 then some localCycle00430 else none) else (if id = 431 then some localCycle00431 else none)))))) else (if id < 442 then (if id < 437 then (if id < 434 then (if id < 433 then (if id = 432 then some localCycle00432 else none) else (if id = 433 then some localCycle00433 else none)) else (if id < 435 then (if id = 434 then some localCycle00434 else none) else (if id < 436 then (if id = 435 then some localCycle00435 else none) else (if id = 436 then some localCycle00436 else none)))) else (if id < 439 then (if id < 438 then (if id = 437 then some localCycle00437 else none) else (if id = 438 then some localCycle00438 else none)) else (if id < 440 then (if id = 439 then some localCycle00439 else none) else (if id < 441 then (if id = 440 then some localCycle00440 else none) else (if id = 441 then some localCycle00441 else none))))) else (if id < 447 then (if id < 444 then (if id < 443 then (if id = 442 then some localCycle00442 else none) else (if id = 443 then some localCycle00443 else none)) else (if id < 445 then (if id = 444 then some localCycle00444 else none) else (if id < 446 then (if id = 445 then some localCycle00445 else none) else (if id = 446 then some localCycle00446 else none)))) else (if id < 450 then (if id < 448 then (if id = 447 then some localCycle00447 else none) else (if id < 449 then (if id = 448 then some localCycle00448 else none) else (if id = 449 then some localCycle00449 else none))) else (if id < 451 then (if id = 450 then some localCycle00450 else none) else (if id < 452 then (if id = 451 then some localCycle00451 else none) else (if id = 452 then some localCycle00452 else none))))))) else (if id < 474 then (if id < 463 then (if id < 458 then (if id < 455 then (if id < 454 then (if id = 453 then some localCycle00453 else none) else (if id = 454 then some localCycle00454 else none)) else (if id < 456 then (if id = 455 then some localCycle00455 else none) else (if id < 457 then (if id = 456 then some localCycle00456 else none) else (if id = 457 then some localCycle00457 else none)))) else (if id < 460 then (if id < 459 then (if id = 458 then some localCycle00458 else none) else (if id = 459 then some localCycle00459 else none)) else (if id < 461 then (if id = 460 then some localCycle00460 else none) else (if id < 462 then (if id = 461 then some localCycle00461 else none) else (if id = 462 then some localCycle00462 else none))))) else (if id < 468 then (if id < 465 then (if id < 464 then (if id = 463 then some localCycle00463 else none) else (if id = 464 then some localCycle00464 else none)) else (if id < 466 then (if id = 465 then some localCycle00465 else none) else (if id < 467 then (if id = 466 then some localCycle00466 else none) else (if id = 467 then some localCycle00467 else none)))) else (if id < 471 then (if id < 469 then (if id = 468 then some localCycle00468 else none) else (if id < 470 then (if id = 469 then some localCycle00469 else none) else (if id = 470 then some localCycle00470 else none))) else (if id < 472 then (if id = 471 then some localCycle00471 else none) else (if id < 473 then (if id = 472 then some localCycle00472 else none) else (if id = 473 then some localCycle00473 else none)))))) else (if id < 484 then (if id < 479 then (if id < 476 then (if id < 475 then (if id = 474 then some localCycle00474 else none) else (if id = 475 then some localCycle00475 else none)) else (if id < 477 then (if id = 476 then some localCycle00476 else none) else (if id < 478 then (if id = 477 then some localCycle00477 else none) else (if id = 478 then some localCycle00478 else none)))) else (if id < 481 then (if id < 480 then (if id = 479 then some localCycle00479 else none) else (if id = 480 then some localCycle00480 else none)) else (if id < 482 then (if id = 481 then some localCycle00481 else none) else (if id < 483 then (if id = 482 then some localCycle00482 else none) else (if id = 483 then some localCycle00483 else none))))) else (if id < 489 then (if id < 486 then (if id < 485 then (if id = 484 then some localCycle00484 else none) else (if id = 485 then some localCycle00485 else none)) else (if id < 487 then (if id = 486 then some localCycle00486 else none) else (if id < 488 then (if id = 487 then some localCycle00487 else none) else (if id = 488 then some localCycle00488 else none)))) else (if id < 492 then (if id < 490 then (if id = 489 then some localCycle00489 else none) else (if id < 491 then (if id = 490 then some localCycle00490 else none) else (if id = 491 then some localCycle00491 else none))) else (if id < 493 then (if id = 492 then some localCycle00492 else none) else (if id < 494 then (if id = 493 then some localCycle00493 else none) else (if id = 494 then some localCycle00494 else none))))))))) else (if id < 577 then (if id < 536 then (if id < 515 then (if id < 505 then (if id < 500 then (if id < 497 then (if id < 496 then (if id = 495 then some localCycle00495 else none) else (if id = 496 then some localCycle00496 else none)) else (if id < 498 then (if id = 497 then some localCycle00497 else none) else (if id < 499 then (if id = 498 then some localCycle00498 else none) else (if id = 499 then some localCycle00499 else none)))) else (if id < 502 then (if id < 501 then (if id = 500 then some localCycle00500 else none) else (if id = 501 then some localCycle00501 else none)) else (if id < 503 then (if id = 502 then some localCycle00502 else none) else (if id < 504 then (if id = 503 then some localCycle00503 else none) else (if id = 504 then some localCycle00504 else none))))) else (if id < 510 then (if id < 507 then (if id < 506 then (if id = 505 then some localCycle00505 else none) else (if id = 506 then some localCycle00506 else none)) else (if id < 508 then (if id = 507 then some localCycle00507 else none) else (if id < 509 then (if id = 508 then some localCycle00508 else none) else (if id = 509 then some localCycle00509 else none)))) else (if id < 512 then (if id < 511 then (if id = 510 then some localCycle00510 else none) else (if id = 511 then some localCycle00511 else none)) else (if id < 513 then (if id = 512 then some localCycle00512 else none) else (if id < 514 then (if id = 513 then some localCycle00513 else none) else (if id = 514 then some localCycle00514 else none)))))) else (if id < 525 then (if id < 520 then (if id < 517 then (if id < 516 then (if id = 515 then some localCycle00515 else none) else (if id = 516 then some localCycle00516 else none)) else (if id < 518 then (if id = 517 then some localCycle00517 else none) else (if id < 519 then (if id = 518 then some localCycle00518 else none) else (if id = 519 then some localCycle00519 else none)))) else (if id < 522 then (if id < 521 then (if id = 520 then some localCycle00520 else none) else (if id = 521 then some localCycle00521 else none)) else (if id < 523 then (if id = 522 then some localCycle00522 else none) else (if id < 524 then (if id = 523 then some localCycle00523 else none) else (if id = 524 then some localCycle00524 else none))))) else (if id < 530 then (if id < 527 then (if id < 526 then (if id = 525 then some localCycle00525 else none) else (if id = 526 then some localCycle00526 else none)) else (if id < 528 then (if id = 527 then some localCycle00527 else none) else (if id < 529 then (if id = 528 then some localCycle00528 else none) else (if id = 529 then some localCycle00529 else none)))) else (if id < 533 then (if id < 531 then (if id = 530 then some localCycle00530 else none) else (if id < 532 then (if id = 531 then some localCycle00531 else none) else (if id = 532 then some localCycle00532 else none))) else (if id < 534 then (if id = 533 then some localCycle00533 else none) else (if id < 535 then (if id = 534 then some localCycle00534 else none) else (if id = 535 then some localCycle00535 else none))))))) else (if id < 556 then (if id < 546 then (if id < 541 then (if id < 538 then (if id < 537 then (if id = 536 then some localCycle00536 else none) else (if id = 537 then some localCycle00537 else none)) else (if id < 539 then (if id = 538 then some localCycle00538 else none) else (if id < 540 then (if id = 539 then some localCycle00539 else none) else (if id = 540 then some localCycle00540 else none)))) else (if id < 543 then (if id < 542 then (if id = 541 then some localCycle00541 else none) else (if id = 542 then some localCycle00542 else none)) else (if id < 544 then (if id = 543 then some localCycle00543 else none) else (if id < 545 then (if id = 544 then some localCycle00544 else none) else (if id = 545 then some localCycle00545 else none))))) else (if id < 551 then (if id < 548 then (if id < 547 then (if id = 546 then some localCycle00546 else none) else (if id = 547 then some localCycle00547 else none)) else (if id < 549 then (if id = 548 then some localCycle00548 else none) else (if id < 550 then (if id = 549 then some localCycle00549 else none) else (if id = 550 then some localCycle00550 else none)))) else (if id < 553 then (if id < 552 then (if id = 551 then some localCycle00551 else none) else (if id = 552 then some localCycle00552 else none)) else (if id < 554 then (if id = 553 then some localCycle00553 else none) else (if id < 555 then (if id = 554 then some localCycle00554 else none) else (if id = 555 then some localCycle00555 else none)))))) else (if id < 566 then (if id < 561 then (if id < 558 then (if id < 557 then (if id = 556 then some localCycle00556 else none) else (if id = 557 then some localCycle00557 else none)) else (if id < 559 then (if id = 558 then some localCycle00558 else none) else (if id < 560 then (if id = 559 then some localCycle00559 else none) else (if id = 560 then some localCycle00560 else none)))) else (if id < 563 then (if id < 562 then (if id = 561 then some localCycle00561 else none) else (if id = 562 then some localCycle00562 else none)) else (if id < 564 then (if id = 563 then some localCycle00563 else none) else (if id < 565 then (if id = 564 then some localCycle00564 else none) else (if id = 565 then some localCycle00565 else none))))) else (if id < 571 then (if id < 568 then (if id < 567 then (if id = 566 then some localCycle00566 else none) else (if id = 567 then some localCycle00567 else none)) else (if id < 569 then (if id = 568 then some localCycle00568 else none) else (if id < 570 then (if id = 569 then some localCycle00569 else none) else (if id = 570 then some localCycle00570 else none)))) else (if id < 574 then (if id < 572 then (if id = 571 then some localCycle00571 else none) else (if id < 573 then (if id = 572 then some localCycle00572 else none) else (if id = 573 then some localCycle00573 else none))) else (if id < 575 then (if id = 574 then some localCycle00574 else none) else (if id < 576 then (if id = 575 then some localCycle00575 else none) else (if id = 576 then some localCycle00576 else none)))))))) else (if id < 618 then (if id < 597 then (if id < 587 then (if id < 582 then (if id < 579 then (if id < 578 then (if id = 577 then some localCycle00577 else none) else (if id = 578 then some localCycle00578 else none)) else (if id < 580 then (if id = 579 then some localCycle00579 else none) else (if id < 581 then (if id = 580 then some localCycle00580 else none) else (if id = 581 then some localCycle00581 else none)))) else (if id < 584 then (if id < 583 then (if id = 582 then some localCycle00582 else none) else (if id = 583 then some localCycle00583 else none)) else (if id < 585 then (if id = 584 then some localCycle00584 else none) else (if id < 586 then (if id = 585 then some localCycle00585 else none) else (if id = 586 then some localCycle00586 else none))))) else (if id < 592 then (if id < 589 then (if id < 588 then (if id = 587 then some localCycle00587 else none) else (if id = 588 then some localCycle00588 else none)) else (if id < 590 then (if id = 589 then some localCycle00589 else none) else (if id < 591 then (if id = 590 then some localCycle00590 else none) else (if id = 591 then some localCycle00591 else none)))) else (if id < 594 then (if id < 593 then (if id = 592 then some localCycle00592 else none) else (if id = 593 then some localCycle00593 else none)) else (if id < 595 then (if id = 594 then some localCycle00594 else none) else (if id < 596 then (if id = 595 then some localCycle00595 else none) else (if id = 596 then some localCycle00596 else none)))))) else (if id < 607 then (if id < 602 then (if id < 599 then (if id < 598 then (if id = 597 then some localCycle00597 else none) else (if id = 598 then some localCycle00598 else none)) else (if id < 600 then (if id = 599 then some localCycle00599 else none) else (if id < 601 then (if id = 600 then some localCycle00600 else none) else (if id = 601 then some localCycle00601 else none)))) else (if id < 604 then (if id < 603 then (if id = 602 then some localCycle00602 else none) else (if id = 603 then some localCycle00603 else none)) else (if id < 605 then (if id = 604 then some localCycle00604 else none) else (if id < 606 then (if id = 605 then some localCycle00605 else none) else (if id = 606 then some localCycle00606 else none))))) else (if id < 612 then (if id < 609 then (if id < 608 then (if id = 607 then some localCycle00607 else none) else (if id = 608 then some localCycle00608 else none)) else (if id < 610 then (if id = 609 then some localCycle00609 else none) else (if id < 611 then (if id = 610 then some localCycle00610 else none) else (if id = 611 then some localCycle00611 else none)))) else (if id < 615 then (if id < 613 then (if id = 612 then some localCycle00612 else none) else (if id < 614 then (if id = 613 then some localCycle00613 else none) else (if id = 614 then some localCycle00614 else none))) else (if id < 616 then (if id = 615 then some localCycle00615 else none) else (if id < 617 then (if id = 616 then some localCycle00616 else none) else (if id = 617 then some localCycle00617 else none))))))) else (if id < 639 then (if id < 628 then (if id < 623 then (if id < 620 then (if id < 619 then (if id = 618 then some localCycle00618 else none) else (if id = 619 then some localCycle00619 else none)) else (if id < 621 then (if id = 620 then some localCycle00620 else none) else (if id < 622 then (if id = 621 then some localCycle00621 else none) else (if id = 622 then some localCycle00622 else none)))) else (if id < 625 then (if id < 624 then (if id = 623 then some localCycle00623 else none) else (if id = 624 then some localCycle00624 else none)) else (if id < 626 then (if id = 625 then some localCycle00625 else none) else (if id < 627 then (if id = 626 then some localCycle00626 else none) else (if id = 627 then some localCycle00627 else none))))) else (if id < 633 then (if id < 630 then (if id < 629 then (if id = 628 then some localCycle00628 else none) else (if id = 629 then some localCycle00629 else none)) else (if id < 631 then (if id = 630 then some localCycle00630 else none) else (if id < 632 then (if id = 631 then some localCycle00631 else none) else (if id = 632 then some localCycle00632 else none)))) else (if id < 636 then (if id < 634 then (if id = 633 then some localCycle00633 else none) else (if id < 635 then (if id = 634 then some localCycle00634 else none) else (if id = 635 then some localCycle00635 else none))) else (if id < 637 then (if id = 636 then some localCycle00636 else none) else (if id < 638 then (if id = 637 then some localCycle00637 else none) else (if id = 638 then some localCycle00638 else none)))))) else (if id < 649 then (if id < 644 then (if id < 641 then (if id < 640 then (if id = 639 then some localCycle00639 else none) else (if id = 640 then some localCycle00640 else none)) else (if id < 642 then (if id = 641 then some localCycle00641 else none) else (if id < 643 then (if id = 642 then some localCycle00642 else none) else (if id = 643 then some localCycle00643 else none)))) else (if id < 646 then (if id < 645 then (if id = 644 then some localCycle00644 else none) else (if id = 645 then some localCycle00645 else none)) else (if id < 647 then (if id = 646 then some localCycle00646 else none) else (if id < 648 then (if id = 647 then some localCycle00647 else none) else (if id = 648 then some localCycle00648 else none))))) else (if id < 654 then (if id < 651 then (if id < 650 then (if id = 649 then some localCycle00649 else none) else (if id = 650 then some localCycle00650 else none)) else (if id < 652 then (if id = 651 then some localCycle00651 else none) else (if id < 653 then (if id = 652 then some localCycle00652 else none) else (if id = 653 then some localCycle00653 else none)))) else (if id < 657 then (if id < 655 then (if id = 654 then some localCycle00654 else none) else (if id < 656 then (if id = 655 then some localCycle00655 else none) else (if id = 656 then some localCycle00656 else none))) else (if id < 658 then (if id = 657 then some localCycle00657 else none) else (if id < 659 then (if id = 658 then some localCycle00658 else none) else (if id = 659 then some localCycle00659 else none))))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 435 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6016)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 0, 6, 1], ![5, 4, 2, 0, 6, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 143 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6017)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 4, 3, 5, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 169 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6018)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 6, 1, 5], ![2, 0, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 442 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6019)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 1, 5], ![2, 0, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 513 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6020)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 5, 6, 1], ![2, 0, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 99 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6021)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 6, 5, 1], ![2, 0, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 464 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6022)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 4, 3, 5, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 5, 1], ![2, 0, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 270 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6023)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 596 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6024)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 5, 6, 1], ![2, 3, 0, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 286 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6025)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 6, 5, 1], ![2, 3, 0, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 312 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6026)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 5, 0, 6, 1], ![2, 3, 4, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 127 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6027)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 4, 5, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 521 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6028)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 454 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6029)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 4, 5, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 126 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6030)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 492 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6031)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 192 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6032)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 5, 4, 3, 2, 6], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 0, 6, 1], ![5, 4, 2, 0, 6, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 252 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6033)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![2, 0, 1, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 450 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6034)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![2, 0, 1, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 359 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6035)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .low6 (![392, 22, 216, 319, 135, 36, 527, 141, 483, 147, 575, 572, 23, 404, 33, 379, 66, 23, 336, 477, 87, 23, 343, 638, 524, 381, 522, 613]) }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6036)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 3, 4]], proof := .low6 (![234, 22, 239, 497, 334, 36, 527, 232, 113, 295, 462, 489, 23, 398, 42, 471, 66, 23, 247, 206, 85, 23, 69, 643, 351, 297, 380, 613]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6037)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 3, 4]], proof := .low6 (![251, 227, 600, 162, 329, 36, 527, 186, 652, 98, 112, 646, 23, 25, 465, 465, 465, 465, 470, 511, 358, 9, 549, 217, 459, 533, 30, 613]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6038)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low6 (![199, 460, 653, 38, 656, 36, 527, 389, 166, 384, 3, 139, 541, 550, 261, 409, 501, 23, 538, 523, 393, 23, 615, 346, 23, 536, 551, 613]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6039)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 4, 3]], proof := .tail 154 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6040)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 4, 3]], proof := .tail 195 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6041)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 4, 3]], proof := .tail 195 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6042)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 195 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6043)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 4, 1, 3]], proof := .low6 (![581, 22, 239, 431, 543, 361, 376, 500, 565, 316, 145, 436, 316, 108, 275, 303, 610, 636, 167, 21, 385, 309, 632, 493, 599, 304, 352, 610]) }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6044)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 4, 1, 3]], proof := .low6 (![581, 227, 473, 505, 399, 361, 376, 382, 316, 316, 145, 316, 316, 25, 255, 465, 465, 465, 323, 125, 150, 171, 278, 402, 585, 559, 205, 642]) }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6045)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 4, 1, 3]], proof := .low6 (![177, 282, 5, 196, 543, 361, 376, 44, 19, 94, 106, 455, 122, 68, 499, 529, 654, 6, 129, 350, 451, 372, 520, 344, 318, 304, 352, 77]) }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6046)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 0, 1, 3]], proof := .low6 (![485, 651, 75, 305, 237, 361, 376, 567, 120, 412, 267, 267, 267, 608, 400, 70, 70, 70, 151, 566, 566, 566, 335, 180, 491, 386, 496, 257]) }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6047)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 0, 1, 3]], proof := .low6 (![419, 54, 292, 305, 241, 361, 376, 554, 428, 299, 81, 81, 81, 290, 488, 258, 149, 535, 56, 173, 367, 67, 335, 180, 491, 146, 158, 453]) }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6048)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 1, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 0, 1, 3]], proof := .low6 (![321, 320, 159, 272, 650, 361, 376, 93, 627, 512, 589, 289, 178, 136, 277, 486, 449, 27, 124, 629, 586, 229, 624, 448, 558, 365, 133, 397]) }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6049)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 3, 6], ![2, 0, 1, 4, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 561 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6050)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 3], ![2, 0, 1, 4, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .low6 (![597, 22, 349, 525, 368, 432, 14, 330, 63, 478, 101, 458, 248, 404, 606, 440, 457, 248, 273, 291, 603, 248, 155, 7, 311, 609, 440, 148]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6051)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 5, 6, 3], ![2, 0, 1, 4, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 413 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6052)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 0, 1, 6, 4, 3], ![2, 0, 1, 5, 4, 3]], proof := .tail 48 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6053)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 0, 6, 1, 4, 3], ![2, 0, 5, 1, 4, 3]], proof := .low6 (![294, 22, 239, 570, 110, 405, 376, 374, 611, 490, 73, 557, 548, 296, 556, 73, 557, 539, 10, 131, 557, 121, 408, 557, 544, 531, 73, 557]) }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6054)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 0, 1, 4, 3]], proof := .low6 (![294, 227, 547, 424, 110, 405, 376, 259, 111, 587, 84, 557, 168, 25, 465, 465, 557, 465, 37, 58, 557, 49, 620, 557, 79, 531, 84, 557]) }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6055)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 0, 1, 4, 3]], proof := .low6 (![199, 460, 463, 519, 110, 405, 182, 212, 498, 441, 91, 557, 228, 514, 396, 657, 557, 530, 617, 181, 557, 593, 416, 557, 375, 531, 502, 557]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6056)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 0, 6, 1, 4, 3], ![2, 0, 5, 4, 1, 3]], proof := .tail 422 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6057)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 0, 4, 1, 3]], proof := .tail 422 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6058)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 0, 4, 1, 3]], proof := .tail 422 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6059)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 1, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 4, 0, 1, 3]], proof := .tail 482 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6060)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 4, 0, 1, 3]], proof := .tail 482 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6061)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 198 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6062)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 4, 6], ![2, 0, 5, 1, 3, 6], ![2, 0, 4, 1, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![40, 22, 103, 43, 528, 32, 281, 175, 387, 474, 116, 362, 80, 569, 191, 65, 362, 226, 308, 65, 362, 226, 518, 362, 188, 115, 579, 362]) }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6063)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 461 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6064)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 469 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6065)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 1, 3, 6], ![2, 0, 4, 1, 3, 5]], proof := .low6 (![219, 22, 410, 481, 15, 432, 14, 552, 53, 655, 403, 8, 452, 218, 238, 179, 457, 452, 246, 373, 430, 452, 433, 510, 204, 446, 29, 148]) }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6066)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 1, 6, 3], ![2, 0, 4, 1, 5, 3]], proof := .low0 (![625, 506, 35, 137, 165, 105, 555, 619, 626, 213, 202, 12, 202, 64, 619, 619, 619, 619, 415, 83, 83, 83, 102, 378, 584, 293, 560, 245]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6067)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 1, 3], ![2, 0, 4, 5, 1, 3]], proof := .tail 576 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6068)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 1, 3], ![2, 0, 5, 4, 1, 3]], proof := .tail 342 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6069)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 0, 4, 1, 3]], proof := .tail 301 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6070)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 0, 4, 1, 3]], proof := .low6 (![199, 164, 144, 196, 107, 361, 376, 377, 537, 1, 345, 11, 537, 76, 388, 271, 51, 262, 100, 280, 468, 456, 507, 265, 326, 224, 649, 203]) }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6071)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 4, 0, 1, 3]], proof := .tail 211 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6072)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 4, 0, 1, 3]], proof := .tail 211 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6073)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 3, 6, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 607 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6074)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![487, 22, 602, 134, 528, 32, 74, 175, 59, 474, 104, 362, 658, 591, 337, 65, 362, 117, 532, 157, 362, 59, 242, 362, 370, 115, 333, 362]) }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6075)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 45 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6076)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 235 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6077)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 3, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 347 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6078)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 1, 6, 3], ![2, 0, 4, 1, 5, 3]], proof := .tail 347 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6079)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 1, 3], ![2, 0, 4, 5, 1, 3]], proof := .tail 314 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6080)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 5]], proof := .low6 (![423, 429, 264, 215, 71, 432, 14, 616, 207, 628, 391, 95, 452, 214, 616, 616, 616, 616, 152, 401, 274, 503, 243, 269, 89, 276, 279, 148]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6081)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 1, 6, 3], ![2, 4, 0, 1, 5, 3]], proof := .low0 (![109, 506, 223, 508, 577, 475, 542, 619, 128, 595, 0, 263, 34, 640, 619, 619, 263, 619, 61, 0, 263, 20, 414, 263, 201, 263, 427, 263]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6082)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 6, 1, 3], ![2, 4, 0, 5, 1, 3]], proof := .tail 576 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6083)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 1, 3], ![2, 4, 5, 0, 1, 3]], proof := .tail 526 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6084)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 1, 3], ![2, 5, 4, 0, 1, 3]], proof := .tail 420 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6085)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 2, 4, 0, 1, 3]], proof := .low6 (![199, 563, 292, 590, 184, 361, 376, 268, 142, 484, 26, 220, 153, 639, 24, 285, 62, 18, 55, 222, 210, 444, 604, 140, 57, 322, 256, 78]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6086)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 1, 6, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 406 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6087)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 5, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![597, 22, 230, 421, 528, 32, 14, 175, 387, 474, 116, 362, 287, 404, 332, 614, 362, 287, 594, 190, 362, 287, 118, 362, 185, 115, 579, 362]) }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6088)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 3, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 313 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6089)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 6, 3], ![2, 0, 1, 4, 5, 3]], proof := .tail 534 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6090)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 3, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 183 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6091)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 1, 6, 3], ![2, 0, 4, 1, 5, 3]], proof := .tail 445 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6092)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 3, 6, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 1, 3], ![2, 0, 4, 5, 1, 3]], proof := .tail 562 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6093)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 5, 6, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 5]], proof := .tail 618 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6094)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 1, 6, 3], ![2, 4, 0, 1, 5, 3]], proof := .tail 445 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6095)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 6, 1, 3], ![2, 4, 0, 5, 1, 3]], proof := .tail 562 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6096)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![2, 4, 5, 0, 1, 3]], proof := .tail 197 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6097)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 1, 5, 6, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 5]], proof := .low6 (![88, 300, 357, 425, 394, 432, 14, 578, 571, 426, 630, 283, 564, 546, 341, 383, 623, 452, 472, 353, 340, 452, 516, 130, 452, 189, 250, 148]) }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6098)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 5, 3]], proof := .low6 (![88, 300, 231, 407, 583, 509, 648, 644, 659, 517, 97, 568, 434, 588, 170, 325, 568, 302, 472, 307, 568, 31, 480, 568, 580, 327, 119, 568]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6099)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 6, 1, 3], ![4, 2, 0, 5, 1, 3]], proof := .low6 (![88, 233, 249, 72, 360, 361, 376, 447, 225, 637, 631, 187, 434, 28, 132, 582, 573, 209, 60, 46, 90, 324, 601, 437, 244, 515, 193, 254]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6100)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 0, 1, 3]], proof := .low6 (![88, 545, 92, 328, 390, 361, 376, 310, 240, 438, 574, 592, 434, 612, 236, 16, 476, 123, 504, 331, 114, 176, 4, 553, 371, 348, 364, 288]) }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6101)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 1, 6, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 0, 1, 3]], proof := .tail 467 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6102)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 1, 6, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 363 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6103)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 4, 3, 1]], proof := .tail 645 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6104)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 0, 6, 1, 4, 3], ![2, 0, 5, 4, 3, 1]], proof := .tail 422 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6105)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 5, 6, 1, 3], ![2, 0, 4, 6, 1, 3], ![2, 0, 4, 5, 3, 1]], proof := .tail 221 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6106)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 3, 4, 5, 6, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 0, 6, 4, 1, 3], ![2, 0, 5, 4, 3, 1]], proof := .tail 284 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6107)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 5, 0, 6, 1, 3], ![2, 4, 0, 6, 1, 3], ![2, 0, 4, 5, 3, 1]], proof := .tail 39 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6108)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 5, 4, 6, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 2, 0, 6, 1, 3], ![4, 2, 0, 6, 1, 3], ![2, 0, 4, 5, 3, 1]], proof := .tail 540 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6109)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 4, 3, 1]], proof := .tail 163 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6110)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 0, 4, 3, 1]], proof := .tail 422 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6111)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 0, 4, 3, 1]], proof := .tail 194 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6112)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 4, 3, 1]], proof := .tail 411 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6113)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 0, 4, 3, 1]], proof := .tail 422 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6114)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 4, 6, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 0, 4, 3, 1]], proof := .low0 (![354, 17, 156, 634, 338, 260, 41, 466, 635, 366, 82, 253, 138, 635, 208, 13, 13, 13, 160, 635, 635, 635, 443, 174, 96, 479, 621, 339]) }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6115)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 0, 6, 1, 3], ![2, 4, 0, 5, 3, 1]], proof := .tail 221 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6116)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 0, 6, 1, 3], ![2, 4, 0, 5, 3, 1]], proof := .tail 540 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6117)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 3, 5, 6, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 0, 6, 1, 3], ![4, 2, 0, 5, 3, 1]], proof := .tail 221 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6118)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 0, 3, 1]], proof := .tail 163 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6119)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 4, 0, 3, 1]], proof := .tail 482 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6120)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 4, 0, 3, 1]], proof := .tail 211 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6121)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 1, 3], ![2, 4, 5, 0, 3, 1]], proof := .tail 605 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6122)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 1, 3], ![2, 5, 4, 0, 3, 1]], proof := .tail 420 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6123)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![2, 4, 5, 0, 3, 1]], proof := .tail 540 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6124)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 0, 3, 1]], proof := .tail 163 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6125)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 4, 0, 3, 1]], proof := .tail 482 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6126)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 2, 4, 0, 3, 1]], proof := .tail 211 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6127)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 6, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![2, 6, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 2, 4, 0, 3, 1]], proof := .low0 (![52, 17, 47, 298, 306, 266, 647, 466, 395, 641, 494, 439, 369, 161, 13, 13, 439, 13, 172, 200, 439, 50, 2, 439, 317, 598, 315, 439]) }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6128)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![4, 2, 5, 0, 3, 1]], proof := .tail 221 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6129)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 1, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 0, 3, 1]], proof := .tail 622 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6130)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 355 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6131)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 6, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![6, 2, 0, 5, 1, 3], ![6, 2, 0, 4, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 607 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6132)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 4, 5, 0, 1], ![2, 0, 6, 1, 5, 4], ![6, 2, 5, 0, 1, 3], ![6, 2, 4, 0, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 406 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6133)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 6, 1, 5, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 0, 1, 3], ![4, 5, 2, 0, 3, 1]], proof := .tail 633 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6134)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 6, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 0, 6, 1, 5, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 0, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 417 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6135)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 3, 0, 1]], proof := .tail 495 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6136)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![2, 6, 0, 1, 4, 3], ![2, 5, 4, 3, 0, 1]], proof := .tail 482 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6137)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 0, 5, 1, 3], ![2, 6, 0, 4, 1, 3], ![2, 5, 4, 3, 0, 1]], proof := .tail 211 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6138)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 5, 6, 0, 1, 3], ![2, 4, 6, 0, 1, 3], ![2, 4, 5, 3, 0, 1]], proof := .tail 86 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6139)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 5, 0, 1, 3], ![2, 6, 4, 0, 1, 3], ![2, 5, 4, 3, 0, 1]], proof := .tail 420 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6140)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 0, 1, 5, 4], ![5, 2, 6, 0, 1, 3], ![4, 2, 6, 0, 1, 3], ![2, 4, 5, 3, 0, 1]], proof := .tail 356 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6141)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 418 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6142)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 2, 0, 1, 4, 3], ![5, 2, 4, 3, 0, 1]], proof := .tail 482 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6143)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6016 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6016 ≤ id.val) (hhigh : id.val < 6144) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6016)) = true := by
  let j : Fin 128 := ⟨id.val - 6016, by omega⟩
  have hsum : 6016 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6016 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard047
